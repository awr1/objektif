import
  objektif / runtime,
  objektif / private / rtutils,
  zero_functional,
  std / macros,
  std / genasts,
  std / strutils

func funcify*(procdef: NimNode): NimNode =
  ## Appends `{.noSideEffect.}` to a call (making it "pure"-ish in Nim terms).
  procdef.addPragma(quote do: noSideEffect)
  procdef

func setify*(name: NimNode): NimNode =
  ## Turns an ident `x` into it's `x=` equivalent for setters.
  nnkAccQuoted.newTree(name, "=".ident)

func subjectType(locality: MessageLocality): NimNode =
  ## Implements equivalent of Obj-C's `+`/`-` locality specifiers.
  case locality
  of Metaclass: (quote do: typedesc)
  of Instance:  (quote do: Alias)

template setupInputs*(argtypes, argnames: untyped; useArgNames: bool): auto =
  let
    # The zfun macros don't like this, so let's seq-ify them first
    cargtypes = argtypes[0 .. ^1]
    cargnames = argnames[0 .. ^1]

    cargs = zip(cargtypes, cargnames) -->
      map((arg: it[1][0], param: it[1][1], `type`: it[0][0]))

    selectable = cargs.zfun:
      map(it.arg.strVal & ":") # ObjC selector form is "x:y:"
      fold("", a & it)         # Join to single string

    identdefs = cargs --> map(newIdentDefs(
      if useArgNames: it.arg else: it.param, it.`type`))

  (cargs, selectable, identdefs)

macro multiarg(class, returns: typed;
               kind:           static[RuntimeSender];
               locality:       static[MessageLocality];
               argtypes:       typed;
               argnames:       untyped): untyped =
  ## "Final-stage" generator macro for muli-argument methods. This is so that
  ## we can pull in typed (resolved) results in from the input parames.
  let
    (cargs, selectable, identdefs) = setupInputs(
      argtypes, argnames, useArgNames = true)

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
      {.pop.}
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
      {.pop.}

  # Finally, add our `input.x`, etc. params to the call
  var callNeedingParams =
    result
      .findChild(it.kind == nnkProcDef and eqIdent(stackname, it.name))
      .findChild(it.kind == nnkStmtList)
      .findChild(it.kind == nnkCall)
  callNeedingParams &= tupleifiedParams

template wrapMultiarg*(class, returns: typed;
                       locality:       MessageLocality;
                       argtypes:       typed;
                       argnames:       untyped): untyped =
  ## Generate multi-argument method wrappers after input parameter resolution.
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

macro property(class, returns: typed;
               kind:           static[RuntimeSender];
               propattrib:     static[set[PropertyAttrib]];
               name:           untyped): untyped =
  ## "Final-stage" generator macro for property getters & setters. This is so
  ## that we can pull in typed (resolved) results in from the input parames.
  let
    castpragma = quote do: funccast
    getter     = zeroarg(class, returns,
                         kind,
                         Instance,
                         castpragma,
                         name).funcify

    setter = block:
      if readwrite in propattrib:
        let
          setstr        = "set" & name.toStrLit.strval.capitalizeASCII & ":"
          setselectable = setstr.newStrLitNode
          setname       = name.setify
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

template wrapProperty*(class, returns: typed;
                       propattrib:     static[set[PropertyAttrib]];
                       name:           untyped): untyped =
  ## Generate instance getters and setters after input parameter resolution.
  property(class, returns,
           kind = toSenderKind(returns),
           propattrib,
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

template wrapBasic*(class, returns: typed;
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
