## Utilities for interfacing with the Objective-C runtime APIs for Apple
## devices. Instead of using `nim objc`, these bind directly to the C
## interfaces for maximum flexibility.

import
  zero_functional,
  std / macros,
  std / genasts,
  std / options,
  std / strutils

{.passL: "-framework Foundation".}
{.passL: "-lobjc".}

type
  SEL*     = distinct pointer
  Class*   = distinct pointer
  IMP      = distinct pointer
  Method   = distinct pointer
  Protocol = distinct pointer
  Ivar     = distinct pointer

  id*           {.pure, inheritable.} = ptr object
  instancetype* {.final.}             = ptr object of id
  Alias[T]                            = T

{.push cdecl, importc, dynlib: "libobjc.A.dylib".}
proc sel_registerName(name: cstring): SEL

{.push varargs.}
proc objc_msgSend      (self: id; name: SEL): id
proc objc_msgSend_fpret(self: id; name: SEL): cdouble
proc objc_msgSend_stret(outp: pointer; self: id; op: SEL)
{.pop.}

proc method_getTypeEncoding(meth: Method): cstring
proc object_getClass       (obj:  id):     Class

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
proc class_getInstanceVariable(obj: id; name: cstring): Ivar
proc ivar_getOffset           (ivar: Ivar):             int
proc object_getIvar           (obj: id; ivar: Ivar):    id
proc object_setIvar           (obj: id; ivar: Ivar; value: id)
{.pop.}

# TODO(awr): std / macrocache approach for caching selectors?
template classify(`type`: typedesc): id =
  var cached {.global.}: id
  if cached == nil: cached = cast[id](objc_getClass($`type`))
  cached

template selectify(name: static[string]): SEL =
  let cached {.global.} = sel_registerName(name)
  cached

template identify[T](obj: T or typedesc[T]): id =
  when obj is typedesc[T]: classify(obj)
  else:                    cast[id](obj)

type
  PropertyTag* = enum
    readwrite, readonly, strong, weak, copy, assign, retain, nonatomic
  MessageLocality = enum
    Metaclass, Instance
  RuntimeSender = enum
    Void, PassType, Identifier, Integer, Float, Super, StructReg, StructPtr

func `[]`(node:      NimNode;
          i:         int or BackwardsIndex;
          expected:  set[NimNodeKind];
          sublength: int = -1): NimNode =
  result = node[i]
  expectKind result, expected
  if sublength > -1:
    expectLen result, sublength

func toSenderKind(desc: typedesc): RuntimeSender =
  ## Determines how a procedure will get called through the runtime (based on
  ## its return type). `macros.sameType` et al. proved not satisfactory, which
  ## is why this takes in a `typedesc` instead of a `NimNode`. Ultimately this
  ## is resolved *prior* to the actual "final-stage" macro expansion.
  when desc is instancetype: PassType
  elif desc is id:           Identifier
  elif desc is cstring:      Integer
  elif desc is SomeInteger:  Integer
  elif desc is bool:         Integer
  elif desc is SomeFloat:    Float
  elif desc is void:         Void
  # See ARM AAPCS64 (Procedure Call Standard) ABI 2023Q1: §6.9 and §6.8.2 says
  # that composite types in excess of 16 bytes are to be dealt as an address
  # "out" parameter instead of being smeared across multiple GPRs.
  elif defined(arm64) and desc.sizeof <= 16: StructReg
  else:                                      StructPtr

template subjectType(locality: MessageLocality): NimNode =
  ## Implements equivalent of Obj-C's `+`/`-` locality specifiers.
  case locality
  of Metaclass: (quote do: typedesc)
  of Instance:  (quote do: Alias)

macro multiarg(class, returns: typed;
               kind:           static[RuntimeSender];
               locality:       static[MessageLocality];
               argtypes:       typed;
               argnames:       untyped): untyped =
  ## "Final-stage" generator macro for muli-argument methods. This is so that
  ## we can pull in typed (resolved) results in from the input parames.
  let
    # The zfun macros don't like this, so let's seq-ify them first
    cargtypes = argtypes[0 .. ^1]
    cargnames = argnames[0 .. ^1]

    cargs = zip(cargtypes, cargnames) -->
      map((arg: it[1][0], param: it[1][1], `type`: it[0][0]))

    selectable = cargs.zfun:
      map(it.arg.strVal & ":") # ObjC selector form is "x:y:"
      fold("", a & it)         # Join to single string

    identdefs = cargs --> map(newIdentDefs(it.arg, it.`type`))

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
          "ret".ident, nnkPtrTy.newTree(returns),
          newEmptyNode())
      else:
        castFormal &= returns
      castFormal &= nnkIdentDefs.newTree(
        "id".ident, "id".bindSym,
        newEmptyNode())
      castFormal &= nnkIdentDefs.newTree(
        "selector".ident, "SEL".bindSym,
        newEmptyNode())
      castFormal &= identdefs
      nnkProcTy.newTree(castFormal, quote do:
        {.cdecl.})

    # bindSym(case kind ...) needs {.dynamicBindSym.}, so w/e
    castableSymbol =
      case kind
      of Void:       bindSym("objc_msgSend")
      of Float:      bindSym("objc_msgSend_fpret")
      of StructPtr:  bindSym("objc_msgSend_stret")
      else:          bindSym("objc_msgSend")

    input            = genSym(kind = nskParam, ident = "input")
    tupleified       = nnkTupleTy.newTree(identdefs)
    tupleifiedParams = cargs --> map(newDotExpr(input, it.arg))

    castedCallable = nnkCast.newTree(toCast, castableSymbol)

    # `quote` confuses the `=>` overload backticks, so we use genAST():
    stackname = nnkAccQuoted.newTree(( # better traces
      "[$1 $2]" % [class.repr, selectable]).ident)

    subjtype = locality.subjectType

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

template prepMultiarg(class, returns: typed;
                      locality:       MessageLocality;
                      argtypes:       typed;
                      argnames:       untyped): untyped =
  multiarg(class, returns,
           kind = toSenderKind(returns),
           locality,
           argtypes, argnames)

template dummycast(body: untyped): untyped = body
template funccast (body: untyped): untyped = {.cast(noSideEffect).}: body

func zeroarg(class, returns:   NimNode;
             kind:             RuntimeSender;
             locality:         MessageLocality;
             castpragma, name: NimNode): NimNode =
  ## Generalized production for zero-argument calls, that being for *both*
  ## "basic" impure methods and proeprty getters, based on a determination of
  ## the internal method's return type.
  let
    selectable = name.toStrLit
    subjtype   = case locality
      of Metaclass: (quote do: typedesc)
      of Instance:  (quote do: Alias)

  case kind
  of PassType:
    quote do:
      proc `name`*[T: `class`](subject: `subjtype`[T]): T =
        `castpragma`:
          cast[T](objc_msgSend(identify(subject),
                               selectify(`selectable`)))
  of StructPtr:
    quote do:
      proc `name`*(subject: `subjtype`[`class`]): `returns` =
        `castpragma`:
          objc_msgSend_stret(addr result,
                             identify(subject),
                             selectify(`selectable`))
  of Void:
    quote do:
      proc `name`*(subject: `subjtype`[`class`]) =
        cast[proc (subject: id; sel: SEL) {.cdecl.}](
          objc_msgSend)(identify(subject),
                        selectify(`selectable`))
  else:
    quote do:
      proc `name`*(subject: `subjtype`[`class`]): `returns` =
        `castpragma`:
          cast[`returns`](objc_msgSend(identify(subject),
                                       selectify(`selectable`)))

func funcify(procdef: NimNode): NimNode =
  ## Appends `{.noSideEffect.}` to a call (making it "pure"-ish in Nim terms).
  procdef.addPragma(quote do: noSideEffect)
  procdef

macro property(class, returns: typed;
               kind:           static[RuntimeSender];
               proptags:       static[set[PropertyTag]];
               name:           untyped): untyped =
  let
    castpragma = quote do: funccast
    getter = zeroarg(class, returns,
                     kind,
                     Instance,
                     castpragma,
                     name).funcify

    setter = block:
      if readwrite in proptags:
        let
          setstr        = "set" & name.toStrLit.strval.capitalizeASCII & ":"
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
        procdef.funcify
      else:
        newEmptyNode()

  result = newStmtList(getter, setter)

template prepProperty(class, returns: typed;
                      proptags:       static[set[PropertyTag]];
                      name:           untyped): untyped =
  ## Generate instance getters and setters after input parameter resolution.
  property(class, returns,
           kind = toSenderKind(returns),
           proptags,
           name)

macro basic(class, returns: typed;
            kind:           static[RuntimeSender];
            locality:       static[MessageLocality];
            name:           untyped): untyped =
  ## Supporting "final-stage" generator macro for zero-argument impure methods
  ## so we can pull in typed (resolved) results in from the params.
  zeroarg(class      = class,
          returns    = returns,
          kind       = kind,
          locality   = locality,
          castpragma = (quote do: dummycast),
          name       = name)

template prepBasic(class, returns: typed;
                   locality:       static[MessageLocality];
                   name:           untyped): untyped =
  ## Sets up zero-argument method calls, e.g. `[NSObject class]`. Codegen-wise
  ## these resemble property getters, without the `{.noSideEffect.}`. Unlike
  ## the calling syntax for multi-argument calls, which uses `x => (y: ())`,
  ## this resembles normal Nim function calls.
  basic(class, returns,
        kind = toSenderKind(returns),
        locality,
        name)

type
  NSObject* = ptr object of id
  NSBundle* = ptr object of NSObject
  NSString* = ptr object of NSObject

prepBasic NSObject, Class, Metaclass, class
prepBasic NSObject, Class, Metaclass, superclass

type
  Prelude = object of RootObj
    returns: NimNode
  PreludeBasic = object of Prelude
    locality, name: NimNode
  PreludeMultiarg = object of Prelude
    argtypes:           seq[NimNode]
    argnames, locality: NimNode
  PreludeProperty = object of Prelude
    proptags, name: NimNode
  Relation = tuple[sub, protocol, super: NimNode]
  Preludes = object
    basics:     seq[PreludeBasic]
    multiargs:  seq[PreludeMultiarg]
    properties: seq[PreludeProperty]

proc relationExtract(xofy: NimNode; forceInfix: bool): Relation =
  ## From a syntax of, e.g. `x of y[z]`, pull out `x`, `y`, and (maybe) `z`.
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

func parseToPreludes*(body: NimNode): Preludes =
  for node in body:
    # Decided to do this in two passes since type information is necesssary
    # yet we are working from an `untyped` context in which scavenging out
    # typeinfo is very difficult.

    case node.kind
    of nnkPrefix: # Class/Instance Method
      let
        prefix = case node[0].strVal
          of "+": Metaclass
          of "-": Instance
          else:   (error("Invalid prefix (must be @/+/-)", node[0]);
                   Instance)

        # Again, bindSym($prefix) needs {.dynamicBindSym.}:
        locality = case prefix
          of Metaclass: bindSym($Metaclass)
          of Instance:  bindSym($Instance)

        # All messages, whether they have zero or more arguments, e.g.:
        #
        #   bindclass NSObject: + (instancetype) alloc + (void) setVersion:
        #     (NSInteger) aVersion
        #
        # will always start out with a nnkCommandNode, consisting of a paren
        # wrapped return node, and either the basic method name or the first
        # argument's identifier.

        identable = {nnkIdent, nnkAccQuoted}
        firstcmd  = node[1, {nnkCommand}, 2]
        returns   = firstcmd[0, {nnkPar}, 1]
        firstname = firstcmd[1, identable]

      if node.len == 2:
        # We know this is a zero-argument message, b/c there is nothing
        # after the `firstcmd` node:
        result.basics &= PreludeBasic(
          returns: returns, locality: locality, name: firstname)

      elif node.len == 3:
        # This is *a lot* weirder and jankier, as while the Nim syntax seems to
        # "accept" this, there's a lot of weird nesting going on. Essentially,
        # arguments repeat themselves in the form of:
        #
        #   newIdentNode(),                 <- ident 1 arg (selector partial)
        #   nnkStmtList.newTree(
        #     nnkCommand.newTree(
        #       nnkPar.newTree(             <- ident 1 type
        #         newIdentNode("id")),
        #       newIdentNode("anArgument"), <- ident 1 param
        #       newIdentNode("afterDelay"), <- ident 2 arg
        #       nnkStmtList.newTree(
        #         nnkCommand.newTree(...

        var
          passing: seq[tuple[arg, param, `type`: NimNode]] =
            @[(arg: `firstname`, param: nil, `type`: nil)]
          cmdpost = node[2, {nnkStmtList}, 1][0, {nnkCommand}]

        while true:
          passing[^1].`type` = cmdpost[0, {nnkPar}]
          if cmdpost[1].kind == nnkExprEqExpr:
            discard # TODO(awr): Overload assignment operation for `userclass`
          else:
            passing[^1].param  = cmdpost[1, identable, 0]

          if cmdpost.len == 2:
            break
          else:
            passing &= (arg: cmdpost[2, identable, 0], param: nil, `type`: nil)
            cmdpost = cmdpost[3, {nnkStmtList}, 1][0, {nnkCommand}]

        let
          # This was weird: the compiler did not like this as a `typed` expr
          # because the idents didn't make sense, but when passed as `untyped`,
          # the macro only gets `nil`.
          #
          # We can't do an array of typedescs, or a mixed tuple containing both
          # typedescs and idents, so we split this into two tuples:
          argtypes = passing --> map(nnkTupleConstr.newTree(it.`type`))

          # This will get passed as an `untyped`:
          argnames = nnkBracket.newTree(passing --> map(nnkTupleConstr.newTree(
            it.arg, it.param)))

        result.multiargs &= PreludeMultiarg(returns:  returns,
                                            argtypes: argtypes,
                                            argnames: argnames,
                                            locality: locality)

    of nnkCommand: # Property (getter/setter)
      let
        atprop = node[0, {nnkCall}]
        prefix = atprop[0, {nnkPrefix}]

      expectIdent prefix[0], "@"
      expectIdent prefix[1], "property"

      let
        # The compiler doesn't seem to parse `var x, y: T` correctly, since
        # here it's not at the beginning of the statement. Instead, of a
        # `nnkVarSection`, we get a `nnkVarTy` containing the first variable
        # name. Additional variable names are in idents right after the
        # `nnkVarTy` node, finally topped by the type, which is wrapped in a
        # `nnkCommandNode`, like thus:
        #
        #   nnkCommand.newTree(
        #     nnkCall.newTree(
        #       nnkPrefix.newTree(
        #         newIdentNode("@"),
        #         newIdentNode("property")),
        #       newIdentNode("readonly"), ...), <- property tags
        #     nnkVarTy.newTree(
        #       newIdentNode("x")),             <- ident 1
        #     newIdentNode("y"), ...            <- ident 2...
        #     nnkStmtList.newTree(
        #       newIdentNode("cstring"))        <- shared type

        # To construct a `set[PropertyTag]` literal:
        specifiers = if atprop.len > 1: atprop[1 .. ^1] else: @[]
        proptags   = nnkCurly.newTree(specifiers)

        first  = node[1, {nnkVarTy}, 1][0, {nnkIdent}]
        others = node[2 .. ^2] --> map((expectKind(it, nnkIdent); it))

        proptype = node[^1, {nnkStmtList}, 1][0, {nnkIdent}]

      result.properties &= ((first & others) --> map(
        PreludeProperty(returns: proptype, proptags: proptags, name: it)))

    else:
      error("Unrecognized directive", node)

macro bindclass*(xofy, body: untyped): untyped =
  # TODO(awr): instantiate class if we haven't already, like `userclass`
  result = newStmtList()

  let
    (sub, _, _) = relationExtract(xofy, forceInfix = false)
    preludes    = parseToPreludes(body)

  for property in preludes.properties:
    let
      returns  = property.returns
      proptags = property.proptags
      name     = property.name

      prep = quote do:
        prepProperty `sub`, `returns`, `proptags`, `name`
    result &= prep

  for basic in preludes.basics:
    let
      returns  = basic.returns
      locality = basic.locality
      name     = basic.name

      prep = quote do:
        prepBasic `sub`, `returns`, `locality`, `name`
    result &= prep

  for basic in preludes.multiargs:
    let
      returns  = basic.returns
      locality = basic.locality
      argnames = basic.argnames
      argtypes = basic.argtypes

      prep = quote do:
        prepMultiarg `sub`, `returns`, `locality`, `argtypes`, `argnames`
    result &= prep

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
        # TODO(awr)
        selectable = ""
        # selectable = formal.signatureExtract.params.toSelectable

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

# Important utility functions for NSString <-> Nim-side Strings. Not sure
# necessarily if they're part of AppKit or UIKit specifically? Or the Obj-C base
# libraries? We link to them anyway insofar as one imports `appkit` or `uikit`,
# so it shouldn't be a problem:

bindclass NSString:
  + (instancetype) stringWithUTF8String: (cstring) nullTerminatedCString
  @property(readonly) var UTF8String: cstring

proc `$`*(s :NSString): string = $(s.UTF8String)
