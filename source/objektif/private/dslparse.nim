## Parse our Objective-C-like Nim DSL (for `userclass` and `bindclass`) into a
## series of "preludes" which define messages and instance variables for any
## particular class derived from `NSObject`. Prelude contents are, after-parse,
## are well-formated `NimNode` collections.

import
  zero_functional,
  std / macros

type
  Prelude* = object of RootObj
    ## Refers to a parsed entity in an class, which always has a type (or void)
    ## associated with it.
    returns*: NimNode
  PreludeBodyKind* = enum
    ## For `userclass`, defines if a particular method body is overriding an
    ## existing method or not. Nominally, in Objective-C, overriding as a
    ## concept is inherently universal - i.e. all methods are virtual and
    ## non-final (barring certain Swift-specific exceptions).
    ##
    ## However, usage of `Override` is somewhat more explicit, will always
    ## use the superclass's exact method argument encoding, and will throw if
    ## we don't match against an existing method.
    Impl, Override
  PreludeBasic* = object of Prelude
    ## Refers to a "zero-argument" message (besides the self-SEL prefix).
    ## `body` is for `userclass` only.
    locality*, body*, bodykind*, name*: NimNode
  PreludeMultiarg* = object of Prelude
    ## Refers to a "multi-argument" message (besides the self-SEL prefix).
    ## `body` is for `userclass` only.
    argtypes*:                              seq[NimNode]
    argnames*, locality*, body*, bodykind*: NimNode
  PreludeProperty* = object of Prelude
    propattrib*, name*: NimNode
  PreludeIvar* = object of Prelude
    ## Specifies an instance variable - in `userclass` the layout/offsets are
    ## automatically generated from the order they appear.
    offset*, name*: NimNode
  Preludes* = object
    # Result from a parsed `bindclass`/`userclass`
    basics*:     seq[PreludeBasic]
    multiargs*:  seq[PreludeMultiarg]
    properties*: seq[PreludeProperty]
    ivars*:      seq[PreludeIvar]

proc relationExtract*(xof: NimNode; forceInfix: bool): tuple[
  sub, protocol, super: NimNode] =
  ## From a syntax of, e.g. `x of y[z]`, pull out `x`, `y`, and (maybe) `z`.
  if forceInfix:
    # Used for user-defined classes:
    expectKind  xof, nnkInfix
    expectLen   xof, 3
    expectIdent xof[0], "of"

  if xof.kind == nnkInfix:
    result.sub      = xof[1]
    result.protocol = if xof[2].kind == nnkBracketExpr: xof[2][1] else: nil
    result.super    = if result.protocol != nil:        xof[2][0] else: xof[2]
    expectKind result.sub,   nnkIdent
    expectKind result.super, nnkIdent
  else:
    expectKind xof, nnkIdent
    result.sub = xof

func parseToPreludes*(body: NimNode; parseMethodBodies: bool): Preludes =
  for node in body:
    # Decided to do this in two passes since type information is necesssary
    # yet we are working from an `untyped` context in which scavenging out
    # typeinfo is very difficult.
    template prefixFirst(node: NimNode) =
      let
        # Again, bindSym($prefix) needs {.dynamicBindSym.}:
        locality {.inject.} = case node[0].strVal
          of "+": (quote do: Metaclass)
          of "-": (quote do: Instance)
          else:   (error("Invalid prefix (must be @/+/-)", node[0]);
                   newEmptyNode())

        # All messages, whether they have zero or more arguments, e.g.:
        #
        #   bindclass NSObject: + (instancetype) alloc + (void) setVersion:
        #     (NSInteger) aVersion
        #
        # will always start out with a nnkCommandNode, consisting of a paren
        # wrapped return node, and either the basic method name or the first
        # argument's identifier.

        identable {.inject.} = {nnkIdent, nnkAccQuoted}
        firstcmd  {.inject.} = node[1, {nnkCommand}, 2]
        returns   {.inject.} = firstcmd[0, {nnkPar}, 1]
        firstname {.inject.} = firstcmd[1, identable]

    case node.kind
    of nnkPrefix: # Class/Instance Method
      node.prefixFirst

      if node.len == 2:
        # We know this is a zero-argument message, b/c there is nothing
        # after the `firstcmd` node:

        if parseMethodBodies:
         error("Missing method body", node)

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
          body    = nil.NimNode

        while true:
          passing[^1].`type` = cmdpost[0, {nnkPar}]
          if cmdpost[1].kind == nnkExprEqExpr:
            if parseMethodBodies:
              expectLen cmdpost, 3
              let
                equation = cmdpost[1]
                kind     = case equation[1, identable].strVal
                  of "impl":     (quote do: Impl)
                  of "override": (quote do: Override)
                  else:
                    (error("no `impl`/`override` directive", equation[1]);
                     newEmptyNode())
              # TODO(awr): handle `kind`?
              passing[^1].param = equation[0, identable]
              body              = cmdpost[2, {nnkStmtList}]
              break
            else:
              error("The `=` directive is for `userclass` only", node)
          else:
            passing[^1].param = cmdpost[1, identable]

          if cmdpost.len == 2: break

          passing &= (arg: cmdpost[2, identable, 0], param: nil, `type`: nil)
          cmdpost = cmdpost[3, {nnkStmtList}, 1][0, {nnkCommand}]

        if parseMethodBodies and body.isNil:
          error("Missing method body", node)

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
                                            locality: locality,
                                            body:     body)
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
        #       newIdentNode("readonly"), ...), <- property attrib
        #     nnkVarTy.newTree(
        #       newIdentNode("x")),             <- ident 1
        #     newIdentNode("y"), ...            <- ident 2...
        #     nnkStmtList.newTree(
        #       newIdentNode("cstring"))        <- shared type

        # To construct a `set[PropertyAttrib]` literal:
        specifiers = if atprop.len > 1: atprop[1 .. ^1] else: @[]
        propattrib = nnkCurly.newTree(specifiers)

        first  = node[1, {nnkVarTy}, 1][0, {nnkIdent}]
        others = node[2 .. ^2] --> map((expectKind(it, nnkIdent); it))

        proptype = node[^1, {nnkStmtList}, 1][0, {nnkIdent}]

      result.properties &= ((first & others) --> map(
        PreludeProperty(returns: proptype, propattrib: propattrib, name: it)))
    of nnkAsgn: # Zero-argument message *with* implementation
      if not parseMethodBodies:
        error("The `=` directive is for `userclass` only", node)

      let
        prefix = node[0, {nnkPrefix}, 2]
        body   = node[1]
      prefix.prefixFirst

      result.basics &= PreludeBasic(
        returns: returns, locality: locality, name: firstname, body: body)
    else:
      error("Unrecognized directive", node)