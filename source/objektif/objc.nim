## Utilities for interfacing with the Objective-C runtime APIs for Apple
## devices. Instead of using `nim objc`, these bind directly to the C
## interfaces for maximum flexibility.

import
  zero_functional,
  std / macros,
  std / genasts,
  std / strutils

{.passL: "-framework Foundation".}
{.passL: "-lobjc".}

type
  SEL      = distinct pointer
  Class    = distinct pointer
  IMP      = distinct pointer
  Method   = distinct pointer
  Protocol = distinct pointer
  Ivar     = distinct pointer

  ID*           {.pure, inheritable.} = ptr object
  InstanceType* {.final.}             = ptr object of ID
  Alias[T]                            = T

{.push cdecl, importc, dynlib: "libobjc.A.dylib".}
proc sel_registerName(name: cstring): SEL

{.push varargs.}
proc objc_msgSend      (self: ID; name: SEL): ID
proc objc_msgSend_fpret(self: ID; name: SEL): cdouble
proc objc_msgSend_stret(outp: pointer; self: ID; op: SEL)
{.pop.}

proc method_getTypeEncoding(meth: METHOD): cstring
proc object_getClass       (obj: ID):      Class

proc class_getClassMethod(class: Class; name: SEL): Method
proc objc_getClass       (name: cstring):           Class

proc class_addMethod(
  class: Class;
  name:  SEL;
  impl:  IMP;
  types: cstring): bool
proc objc_allocateClassPair(
  class:      Class;
  name:       cstring;
  extraBytes: csize_t): Class
proc objc_registerClassPair(class: Class)

proc objc_getProtocol        (name: cstring):                 Protocol
proc class_addProtocol       (class: Class; proto: Protocol): bool
proc class_conformsToProtocol(class: Class; proto: Protocol): bool

proc class_addIvar(
  class:     Class;
  name:      cstring;
  size:      csize_t;
  alignment: uint8;
  types:     cstring): bool
proc class_getInstanceVariable(obj: ID; name: cstring): Ivar
proc ivar_getOffset           (ivar: Ivar):             int
proc object_getIvar           (obj: ID; ivar: Ivar):    ID
proc object_setIvar           (obj: ID; ivar: Ivar; value: ID)
{.pop.}

# TODO(awr): std / macrocache approach for caching selectors?
template classify(`type`: typedesc): ID =
  var cached {.global.}: ID
  if cached == nil: cached = cast[ID](objc_getClass($`type`))
  cached

template selectify(name: static[string]): SEL =
  let cached {.global.} = sel_registerName(name)
  cached

template identify[T](obj: T or typedesc[T]): ID =
  when obj is typedesc[T]: classify(obj)
  else:                    cast[ID](obj)

type
  PropertyAccess* = enum
    NonProperty, Readonly, Writable
  MessageLocality = enum
    Metaclass, Instance
  RuntimeSender = enum
    Void, PassType, Identifier, Integer, Float, Super, StructReg, StructPtr

func toSenderKind(desc: typedesc): RuntimeSender =
  when desc is InstanceType: PassType
  elif desc is ID:           Identifier
  elif desc is cstring:      Integer
  elif desc is SomeInteger:  Integer
  elif desc is bool:         Integer
  elif desc is SomeFloat:    Float
  elif desc is void:         Void
  # See ARM AAPCS64 (Procedure Call Standard) ABI 2023Q1: §6.9 and §6.8.2
  # elaborates that composite types in excess of 16 bytes are to be dealt
  # as an address out parameter instead of being smeared across multiple
  # standard GPRs.
  elif defined(arm64) and desc.sizeof <= 16: StructReg
  else:                                      StructPtr

func toSelectable(params: seq[NimNode]): string =
  params.zfun:
    map(it[0 .. ^3])     # Omit type and default value node
    flatten()            # Convert @[@[x, y]] --> @[x, y]
    map(it.strVal & ":") # ObjC selector form is "x:y:"
    fold("", a & it)     # Finally, join to single string

func signatureExtract(formal: NimNode): tuple[params:  seq[NimNode],
                                              returns: NimNode] =
  (params: formal[1 .. ^1], returns: formal[0])

macro returnType(signature: typed): untyped =
  # sameType() is bugged in the way it works with bound symbols based on how
  # the symbol was acquired in the first place, thus this layer of indirection
  # is needed (and why this can't be all accomplished with a single macro).
  # This is also not needed inside of toSenderProc() specifically, only by
  # virtue of the RuntimeSender determination.
  let extract = signature.findChild(it.kind == nnkFormalParams)
                         .signatureExtract
  if extract.returns.kind == nnkEmpty:
    quote do: void
  else:
    extract.returns

macro toSenderProc*(kind:      static[RuntimeSender];
                    locality:  static[MessageLocality];
                    class:     untyped;
                    signature: typed): untyped =
  # TODO(awr): Would be nice to ensure basic schema
  let
    extract = signature.findChild(it.kind == nnkFormalParams)
                       .signatureExtract

    toCast = block:
      # Params to newTree are all single node, thus imperative style.
      var castFormal = nnkFormalParams.newTree
      case kind
      of PassType:
        # Works the same way `instancetype` does in Obj-C.
        castFormal &= class
      of StructPtr:
        # In the case of calls to `objc_msgSend_stret()`, i.e. raw C struct
        # returns, the return value is actually void and instead an out param
        # precedes the ID and selector params which takes in an address in
        # which to fill in with the structural "return value."
        castFormal &= newEmptyNode()
        castFormal &= nnkIdentDefs.newTree(
          "ret".ident, nnkPtrTy.newTree(extract.returns),
          newEmptyNode())
      else:
        castFormal &= extract.returns
      castFormal &= nnkIdentDefs.newTree(
        "id".ident, "ID".bindSym,
        newEmptyNode())
      castFormal &= nnkIdentDefs.newTree(
        "selector".ident, "SEL".bindSym,
        newEmptyNode())
      castFormal &= extract.params
      nnkProcTy.newTree(castFormal, quote do:
        {.cdecl.})

    selectable = extract.params.toSelectable

    # bindSym(case kind ...) needs {.dynamicBindSym.}, so w/e
    castableSymbol =
      case kind
      of Void:       bindSym("objc_msgSend")
      of Identifier: bindSym("objc_msgSend")
      of Integer:    bindSym("objc_msgSend")
      of Float:      bindSym("objc_msgSend_fpret")
      of StructPtr:  bindSym("objc_msgSend_stret")
      else:          bindSym("objc_msgSend")

    # Needed b/c compiler will complain due to symbols being bound as params
    # which is inappropriate for field reusage when used as tuples
    desymedParams = extract.params.zfun(defs):
      map:
        desymed = defs.zfun(node):
          map:
            if node.kind == nnkSym:
              node.strVal.ident
            else:
              node
        nnkIdentDefs.newTree(desymed)

    input            = genSym(kind = nskParam, ident = "input")
    tupleified       = nnkTupleTy.newTree(desymedParams)
    tupleifiedParams = extract.params.zfun:
      map(it[0 .. ^3])           # Omit type and default value node
      flatten()                  # Convert @[@[x, y]] --> @[x, y]
      map(newDotExpr(input, it)) # To exprs of form `input.x`, etc.

    castedCallable = nnkCast.newTree(toCast, castableSymbol)

    # `quote` confuses the `=>` overload backticks, so we use genAST():
    returns   = extract.returns        # genAST() doesn't like dot exprs
    stackname = nnkAccQuoted.newTree(( # better traces
      "[$1 $2]" % [class.repr, selectable]).ident)

    # Implement `+`/`-` (i.e. class/instance methods respectively)
    subjtype =
      case locality
      of Metaclass: (quote do: typedesc)
      of Instance:  (quote do: Alias)

  if kind == PassType:
    result = genAST(class,
                    subjtype,
                    input,
                    tupleified,
                    castedCallable,
                    selectable,
                    stackname):
      proc stackname[T: class](subject: subjtype[T];
                               input:   tupleified): T =
        castedCallable(identify(subject), selectify(selectable))

      {.push stackTrace: off.}
      proc `=>`*[T: class](subject: subjtype[T];
                           input:   tupleified): T =
        stackname(subject, input)
      {.push stackTrace: on.}
  else:
    result = genAST(class,
                    subjtype,
                    input,
                    tupleified,
                    returns,
                    castedCallable,
                    selectable,
                    stackname):
      proc stackname[T: class](subject: subjtype[T];
                               input:   tupleified): `returns` =
        castedCallable(identify(subject), selectify(selectable))

      {.push stackTrace: off.}
      proc `=>`*(subject: subjtype[class];
                 input:   tupleified): `returns` =
        stackname(subject, input)
      {.push stackTrace: on.}

  # Finally, add our `input.x`, etc. params to the call
  var callNeedingParams =
    result
      .findChild(it.kind == nnkProcDef and eqIdent(stackname, it.name))
      .findChild(it.kind == nnkStmtList)
      .findChild(it.kind == nnkCall)
  callNeedingParams &= tupleifiedParams

template imessage*(class: untyped; signature: typed): untyped =
  toSenderProc(toSenderKind(returnType(signature)), Instance, class, signature)

template cmessage*(class: untyped; signature: typed): untyped =
  toSenderProc(toSenderKind(returnType(signature)), Metaclass, class, signature)

template dummycast(body: untyped): untyped = body
template funccast (body: untyped): untyped = {.cast(noSideEffect).}: body

macro toZeroargProcs(kind:     static[RuntimeSender];
                     class:    typed;
                     returns:  typed;
                     locality: static[MessageLocality];
                     access:   static[PropertyAccess];
                     name:     untyped): untyped =
  let
    selectable = name.toStrLit

    subjtype =
      case locality
      of Metaclass: (quote do: typedesc)
      of Instance:  (quote do: Alias)

    castpragma =
      if access == NonProperty: (quote do: dummycast)
      else:                     (quote do: funccast)

    getter = block:
      var procdef = block:
        if kind == PassType:
          quote do:
            proc `name`*[T: `class`](subject: `subjtype`[T]): T =
              `castpragma`:
                cast[T](objc_msgSend(identify(subject),
                                    selectify(`selectable`)))
        elif kind == StructPtr:
          quote do:
            proc `name`*(subject: `subjtype`[`class`]): `returns` =
              `castpragma`:
                objc_msgSend_stret(addr result,
                                  identify(subject),
                                  selectify(`selectable`))
        elif kind == Void:
          if access != NonProperty:
            error("Property semantics declared on a non-property", class)
          quote do:
            proc `name`*(subject: `subjtype`[`class`]) =
              cast[proc (subject: ID; sel: SEL) {.cdecl.}](
                objc_msgSend)(identify(subject),
                              selectify(`selectable`))
        else:
          quote do:
            proc `name`*(subject: `subjtype`[`class`]): `returns` =
              `castpragma`:
                cast[`returns`](objc_msgSend(identify(subject),
                                            selectify(`selectable`)))
      if access != NonProperty: procdef.addPragma(quote do: noSideEffect)
      procdef

    setter = block:
      if access == Writable:
        let
          setstr        = "set" & selectable.strval.capitalizeASCII & ":"
          setselectable = setstr.newStrLitNode
          setname       = nnkAccQuoted.newTree(name, "=".ident)
        var procdef = quote do:
          proc `setname`*(subject: var `class`; value: `returns`) =
            `castpragma`:
              let valueSubject = subject # de-ptrize
              cast[proc (subject: ID; sel: SEL; value: `returns`) {.cdecl.}](
                objc_msgSend)(identify(valueSubject),
                              selectify(`setselectable`),
                              value)
        if access != NonProperty: procdef.addPragma(quote do: noSideEffect)
        procdef
      else:
        newEmptyNode()
  result = newStmtList(getter, setter)

template zeroarg(class:    typed;
                 returns:  typed;
                 locality: static[MessageLocality];
                 access:   static[PropertyAccess];
                 name:     untyped): untyped =
  # Because property procedures operate on the same message passing mechanism
  # as normal `[x y:0 z:1...]` calls, we consider them more or less synonymous
  # with zero-arg messages, like `[NSObject alloc]`. The only difference is
  # that properties will be considered essentially pure.
  toZeroargProcs(
    toSenderKind(returns),
    class,
    returns,
    locality,
    access,
    name)

type
  NSObject* = ptr object of ID
  NSBundle* = ptr object of NSObject
  NSString* = ptr object of NSObject

zeroarg NSObject, Class, Metaclass, NonProperty, class
zeroarg NSObject, Class, Metaclass, NonProperty, superclass

# Important utility functions for NSString <-> Nim-side Strings. Not sure
# necessarily if they're part of AppKit or UIKit specifically? Or the Obj-C
# base libraries? We link to them anyway insofar as one imports `appkit`
# or `uikit`, so it shouldn't be a problem:
zeroarg NSString, cstring, Instance, Readonly, UTF8String
cmessage NSString, proc (stringWithUTF8String: cstring): InstanceType
proc `$`*(s :NSString): string = $(s.UTF8String)

proc relationExtract(xofy: NimNode; forceInfix: bool):
  tuple[sub, protocol, super: NimNode] =
  if forceInfix:
    # Used for user-defined classes:
    expectKind  xofy, nnkInfix
    expectLen   xofy, 3
    expectIdent xofy[0], "of"

  if xofy.kind == nnkInfix:
    result.sub      = xofy[1]
    result.protocol = if xofy[2].kind == nnkBracketExpr: xofy[2][1] else: nil
    result.super    = if result.protocol != nil:         xofy[2][0] else: xofy[2]
    expectKind result.sub,   nnkIdent
    expectKind result.super, nnkIdent
  else:
    expectKind xofy, nnkIdent
    result.sub = xofy

proc generateClass(xofy, body: NimNode): NimNode =
  let
    # Let's unpack this to play nice with `quote`:
    (sub, protocol, super) = relationExtract(xofy, forceInfix = true)

    subnamelit = sub.strVal
    subname    = genSym(ident = "subname" & subnameLit)
    superclass = genSym(ident = "superclass")
    subclass   = genSym(ident = "subclass")
    metaclass  = genSym(ident = "metaclass")
    proto      = genSym(ident = "proto")
    protoname  = if protocol != nil: protocol.strVal else: ""

  # In Objective-C, metaclasses compliment all classes - the metaclass is a
  # somewhat more obscure mecahnism used for handling "static" messages not
  # associated with a class instance itself.
  result = quote do:
    when not `sub` is `super`:
      {.error: "`userclass` relation was declared incorrectly.".}

    let
      `subname`    = `subnamelit`
      `superclass` = `super`.class
      `subclass`   = objc_allocateClassPair(`superclass`, `subname`.cstring, 0)
      `metaclass`  = object_getClass(cast[ID](`subclass`))

  if protocol != nil:
    expectKind protocol, nnkIdent
    let
      protoname = protocol.strVal
      protonew  = quote do:
        let `proto` = objc_getProtocol(`protoname`.cstring)
    result &= protonew

  var ivars, meths = newStmtList()
  for cmd in body:
    if cmd.kind == nnkVarSection:
      for defs in cmd:
        let
          varnames = defs[0 .. ^3]
          vartype  = defs[^2]
          varval   = defs[^1]
        expectKind varval, nnkEmpty
        # TODO(awr): expect shared type to be concrete
        # TODO(awr): property vs ivar on global (i.e. `var x*`)?
        for name in varnames:
          let
            namelit  = name.strVal
            ivarname = genSym(ident = "ivar" & nameLit)
            setname  = nnkAccQuoted.newTree(name, "=".ident)
            ivarnew  = quote do:
              let `ivarname` = `namelit`
              if not class_addIvar(`subclass`,
                                   `ivarname`.cstring,
                                   sizeof(`vartype`).csize_t,
                                   alignof(`vartype`).uint8,
                                   "?".cstring):
                raise OSError.newException("Couldn't add ivar `$1` to `$2`" %
                  [`ivarname`, `subname`])

              proc `name`*(subject: `sub`): `vartype` =
                # TODO(awr): cache this
                let ivar = class_getInstanceVariable(
                  classify(`sub`), `ivarname`.cstring)
                when `vartype` is ID:
                  cast[variables.sharedType](object_getIvar(subject, ivar))
                else:
                  let offset = ivar_getOffset(ivar)
                  cast[ptr `vartype`](
                    cast[int](subject) + offset)[]

              proc `setname`*(subject: var `sub`; value: `vartype`) =
                # TODO(awr): cache this
                let ivar = class_getInstanceVariable(
                  classify(`sub`), `ivarname`.cstring)
                when `vartype` is ID:
                  object_setIvar(subject, ivar, value)
                else:
                  let offset = ivar_getOffset(ivar)
                  cast[ptr `vartype`](
                    cast[int](subject) + offset)[] = value
          ivars &= ivarnew

    elif (let isOverride  = cmd[0].eqIdent("override");
          let isUnderived = cmd[0].eqIdent("underived");
          isOverride or isUnderived):
      let lambda = cmd[1]
      expectKind lambda, nnkLambda

      let
        def  = nnkProcDef.newTree
        decl = nnkProcDef.newTree
      lambda.copyChildrenTo(def)
      lambda.copyChildrenTo(decl)

      let
        defsym = genSym(kind = nskProc, ident = "overrideRaw")
        formal   = def.findChild(it.kind == nnkFormalParams)
        # Implicit `self` param, i.e. proc (self: Foo; ...)
        self = newIdentDefs(
          name = newIdentNode("self"),
          kind = sub)
        sel = newIdentDefs(
          name = newIdentNode("selector"),
          kind = bindSym("SEL"))
        selectable = formal.signatureExtract.params.toSelectable

      formal.insert(1, self)
      formal.insert(2, sel)
      decl[^1] = newEmptyNode()

      def.addPragma("cdecl".ident)
      def.name = defsym

      let
        pullpush =
          if isOverride:
            quote do:
              let
                selector = selectify(`selectable`)
                meth     = (sub:  class_getClassMethod(`subclass`,  selector),
                            meta: class_getClassMethod(`metaclass`, selector))
                encoding = (sub:  method_getTypeEncoding(meth.sub),
                            meta: method_getTypeEncoding(meth.meta))
              discard class_addMethod(
                `metaclass`, selector, cast[IMP](`defsym`), encoding.meta)
              discard class_addMethod(
                `subclass`, selector, cast[IMP](`defsym`), encoding.sub)
          else: # Method is "underived"
            quote do:
              let selector = selectify(`selectable`)
              # TODO(awr): This requires enconding a method signature against
              # the Obj-C specification. Not impossible but needs some doing

        submission = quote do:
          `def`
          `pullpush`
          message `sub`, `decl`

      meths &= submission

  let registration = quote do:
    `ivars`
    objc_registerClassPair(`subclass`) # No ivars, only method-adding after
    `meths`

  result &= registration

  if protocol != nil:
    # While protocols are in Obj-C primarily supposed to be used for static
    # typechecking, this is kinda useless to us as we are primarily just
    # leveraging the Obj-C runtime environment in specific as opposed to the
    # entire Obj-C semantic stack.
    #
    # That being said, we can still test protocol conformance against the
    # runtime, given certain restrictions. One of the weirder things about the
    # spec is that it clarifies that the runtime will drop the creation of
    # protocol objects that aren't used in the code. Since none of our code is
    # actually Obj-C, this means that a conformance check is rendered useless,
    # so we check for nil.
    #
    # As for why this was done in the first place is unclear: maybe to reduce
    # binary bloat, but even that doesn't make complete sense.

    let conformance = quote do:
      discard class_addProtocol(`subclass`, `proto`)
      if cast[pointer](`proto`) != nil and not class_conformsToProtocol(
        `subclass`, `proto`):
        raise OSError.newException("Couldn't conform `$1` to protocol `$2`" %
          [`subname`, `protoname`])

    result &= conformance

macro userclass*(xofy, body: untyped): untyped =
  generateClass(xofy, body)

macro bindclass*(xofy, body: untyped): untyped =
  let (sub, _, super) = relationExtract(xofy, forceInfix = false)
  result = newStmtList()

  # TODO(awr): instantiate class if we haven't already, like `userclass`
  for node in body:
    # Decided to do this in two passes since type information is necesssary
    # yet we are working from an `untyped` context in which scavenging out
    # typeinfo is very difficult.
    if node.kind == nnkPrefix:
      let
        prefix   = node[0].strVal
        locality = case prefix
          of "+": bindSym("Metaclass")
          of "-": bindSym("Instance")
          else:   (error("Invalid prefix (must be +/-)", node[0]);
                   newEmptyNode())
      if (let zerosig = node[1]; zerosig.kind == nnkCall):
        # Looks like a "call" because the syntax is e.g. `+ x(): int`
        let
          tailend   = node[^1]
          name      = zerosig.findChild(it.kind == nnkIdent)
          returns   = tailend.findChild(it.kind == nnkIdent)

        expectLen node,    3
        expectLen zerosig, 1

        # We feed this through a new macro in order to obtain latent type
        # information (also it's less work as this used to work with a
        # different syntax alltogether):
        let message = quote do:
          zeroarg `sub`, `returns`, `locality`, NonProperty, `name`
        echo message.astGenRepr
        result &= message