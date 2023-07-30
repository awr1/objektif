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
    Readonly, Writable
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
                    class:     typed;
                    signature: typed): untyped =
  # TODO(awr): Would be nice to ensure basic schema
  let
    extract = signature.findChild(it.kind == nnkFormalParams)
                       .signatureExtract

    toCast = block:
      # Params to newTree are all single node, thus imperative style.
      var castFormal = nnkFormalParams.newTree
      if kind == PassType:
        # Works the same way `instancetype` does in Obj-C.
        castFormal &= class
      elif kind == StructPtr:
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
  let
    returns   = extract.returns        # genAST() doesn't like dot exprs
    stackname = nnkAccQuoted.newTree(( # better traces
      "[$1 $2]" % [class.repr, selectable]).ident)

  if kind == PassType:
    result = genAST(class,
                    input,
                    tupleified,
                    castedCallable,
                    selectable,
                    stackname):
      proc stackname[T: class](subject: T or typedesc[T];
                               input:   tupleified): T =
        castedCallable(identify(subject), selectify(selectable))

      {.push stackTrace: off.}
      proc `=>`*[T: class](subject: T or typedesc[T];
                           input:   tupleified): T =
        stackname(subject, input)
      {.push stackTrace: on.}
  else:
    result = genAST(class,
                    input,
                    tupleified,
                    returns,
                    castedCallable,
                    selectable,
                    stackname):
      proc stackname[T: class](subject: T or typedesc[T];
                               input:   tupleified): `returns` =
        castedCallable(identify(subject), selectify(selectable))

      {.push stackTrace: off.}
      proc `=>`*(subject: class or typedesc[class];
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

template message*(class: typed; signature: typed): untyped =
  toSenderProc(toSenderKind(returnType(signature)), class, signature)

macro propertyType(content: untyped): untyped =
  # For similar reasons to returnType()...
  content[2]

macro toPropertyProcs(kind:    static[RuntimeSender];
                      class:   typed;
                      content: untyped;
                      access:  static[PropertyAccess]): untyped =
  expectKind  class,      nnkSym
  expectKind  content,    nnkInfix
  expectIdent content[0], "->"

  let
    name           = content[1]
    returns        = content[2]
    selectable     = name.toStrLit

    getter = block:
      if kind == PassType:
        quote do:
          proc `name`*[T: `class`](subject: T or typedesc[T]): T =
            cast[T](objc_msgSend(identify(subject),
                                 selectify(`selectable`)))
      elif kind == StructPtr:
        quote do:
          proc `name`*(subject: `class` or typedesc[`class`]): `returns` =
            objc_msgSend_stret(addr result,
                               identify(subject),
                               selectify(`selectable`))
      elif kind == Void:
        quote do:
          proc `name`*(subject: `class` or typedesc[`class`]) =
            cast[proc (subject: ID; sel: SEL) {.cdecl.}](
              objc_msgSend)(identify(subject),
                            selectify(`selectable`))
      else:
        quote do:
          proc `name`*(subject: `class` or typedesc[`class`]): `returns` =
            cast[`returns`](objc_msgSend(identify(subject),
                                         selectify(`selectable`)))

    setter = block:
      if access == Writable:
        let
          setstr        = "set" & selectable.strval.capitalizeASCII & ":"
          setselectable = setstr.newStrLitNode
          setname       = nnkAccQuoted.newTree(name, "=".ident)
        quote do:
          proc `setname`*(subject: var `class`; value: `returns`) =
            let valueSubject = subject # de-ptrize
            cast[proc (subject: ID; sel: SEL; value: `returns`) {.cdecl.}](
              objc_msgSend)(identify(valueSubject),
                            selectify(`setselectable`),
                            value)
      else:
        newEmptyNode()

  result = newStmtList(getter, setter)

template property*(class:   typed;
                   content: untyped;
                   access:  static[PropertyAccess] = Readonly): untyped =
  toPropertyProcs(toSenderKind(propertyType(content)), class, content, access)

type
  NSObject* = ptr object of ID
  NSBundle* = ptr object of NSObject
  NSString* = ptr object of NSObject

property NSObject, class      -> Class
property NSObject, superclass -> Class

# Important utility functions for NSString <-> Nim-side Strings. Not sure
# necessarily if they're part of AppKit or UIKit specifically? Or the Obj-C
# base libraries? We link to them anyway insofar as one imports `appkit`
# or `uikit`, so it shouldn't be a problem:
property NSString, UTF8String -> cstring
message  NSString, proc (stringWithUTF8String: cstring): InstanceType
proc `$`*(s :NSString): string = $(s.UTF8String)

proc generateClass(xofy, body: NimNode): NimNode =
  expectKind xofy, nnkInfix
  expectIdent xofy[0], "of"

  let
    sub      = xofy[1]
    protocol = if xofy[2].kind == nnkBracketExpr: xofy[2][1] else: nil
    super    = if protocol != nil:                xofy[2][0] else: xofy[2]
  expectKind sub,   nnkIdent
  expectKind super, nnkIdent

  let
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

    elif cmd[0].eqIdent("override"):
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

      # Finally, actually override the method in the runtime:
      let override = quote do:
        `def`
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
        message `sub`, `decl`

      meths &= override

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

macro userclass*(xofy, body: untyped): untyped = generateClass(xofy, body)
