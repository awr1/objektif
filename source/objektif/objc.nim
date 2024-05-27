## Utilities for interfacing with the Objective-C runtime APIs for Apple
## devices. Instead of using `nim objc`, these bind directly to the C
## interfaces for maximum flexibility.

import
  objektif / runtime,
  objektif / private / rtutils,
  objektif / private / dslparse,
  objektif / private / wrapmsg,
  zero_functional,
  std / macros,
  std / genasts,
  std / options,
  std / strutils,
  std / tables

export
  runtime,
  rtutils.PropertyAttrib

type
  NSBundle* = ptr object of NSObject
  NSString* = ptr object of NSObject

wrapBasic NSObject, Class, Metaclass, class
wrapBasic NSObject, Class, Metaclass, superclass

macro bindclass*(xofy, body: untyped): untyped =
  # TODO(awr): instantiate (NOT declare) class if we haven't already, similar to
  # how `userclass` works
  let
    (sub, _, _) = relationExtract(xofy, forceInfix        = false)
    preludes    = parseToPreludes(body, parseMethodBodies = false)
    properties = block:
      var list = newStmtList()
      for it in preludes.properties:
        let
          returns    = it.returns
          propattrib = it.propattrib
          name       = it.name
          wrap       = quote do:
            wrapProperty `sub`, `returns`, `propattrib`, `name`
        list &= wrap
      list

    basics = block:
      var list = newStmtList()
      for it in preludes.basics:
        let
          returns  = it.returns
          locality = it.locality
          name     = it.name
          wrap     = quote do:
            wrapBasic `sub`, `returns`, `locality`, `name`
        list &= wrap
      list

    multiargs = block:
      var list = newStmtList()
      for it in preludes.multiargs:
        let
          returns  = it.returns
          locality = it.locality
          argnames = it.argnames
          argtypes = it.argtypes
          wrap     = quote do:
            wrapMultiarg `sub`, `returns`, `locality`, `argtypes`, `argnames`
        list &= wrap
      list

  result = quote do:
    when not declared(`sub`):
      {.error: "Type must be declared by user before Obj-C bindings made".}

    `properties`
    `basics`
    `multiargs`

macro userclass*(xofy, body: untyped): untyped =
  let
    # Let's unpack this to play nice with `quote`:
    (sub, protocol, super) = relationExtract(xofy, forceInfix        = true)
    preludes               = parseToPreludes(body, parseMethodBodies = true)

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
    when not declared(`sub`):
      {.error: "Type must be declared by user before Obj-C bindings made".}

    when not `sub` is `super`:
      {.error: "`userclass` relation was declared incorrectly".}

    let
      `subname`    = `subnamelit`
      `superclass` = `super`.class
      `subclass`   = objc_allocateClassPair(`superclass`, `subname`.cstring, 0)
      `metaclass`  = object_getClass(cast[id](`subclass`))

  if protocol != nil:
    expectKind protocol, nnkIdent
    let
      protoname = protocol.strVal
      protonew  = quote do:
        let `proto` = objc_getProtocol(`protoname`.cstring)
    result &= protonew

  func formalize(returns: NimNode; identdefs: seq[NimNode] = @[]): seq[NimNode] =
    # For runtime-compat proc definition:
    let
      # All Obj-C messages begin with `(self: sub; _cmd: SEL)`. Because of the
      # way the Obj-C runtime works, you end up with `self` for both instance
      # and metaclass methods:
      self = newIdentDefs(name = "self".ident,
                          kind = sub)
      cmd  = newIdentDefs(name = nnkAccQuoted.newTree("_cmd".ident),
                          kind = (quote do: SEL))
    @[returns, self, cmd] & identdefs

  let
    properties = block:
      var list = newStmtList()
      for it in preludes.properties:
        discard
      list

    ivars = block:
      # TODO(awr): this is *WRONG*, as this is *NOT* an ivar but a property.
      var list = newStmtList()
      for it in preludes.ivars:
        let
          returns    = it.returns
          name       = it.name
          setname    = name.setify

          # TODO(awr): is type concrete?
          ivarnew = quote do:
            if not class_addIvar(`subclass`,
                                 `name`.cstring,
                                 sizeof(`returns`).csize_t,
                                 alignof(`returns`).uint8,
                                 # TODO(awr): proper type encoding
                                 "?".cstring):
              raise OSError.newException("Couldn't add ivar `$1` to `$2`" %
                [`name`, `subname`])

            proc `name`*(subject: `sub`): `returns` =
              # TODO(awr): cache this
              let ivar = class_getInstanceVariable(
                classify(`sub`), `name`.cstring)
              when `returns` is id:
                cast[variables.sharedType](object_getIvar(subject, ivar))
              else:
                let offset = ivar_getOffset(ivar)
                cast[ptr `returns`](cast[int](subject) + offset)[]

            proc `setname`*(subject: var `sub`; value: `returns`) =
              # TODO(awr): cache this
              let ivar = class_getInstanceVariable(
                classify(`sub`), `returns`.cstring)
              when `returns` is id:
                object_setIvar(subject, ivar, value)
              else:
                let offset = ivar_getOffset(ivar)
                cast[ptr `returns`](cast[int](subject) + offset)[] = value

        list &= ivarnew
      list

    basics = block:
      var list = newStmtList()
      for it in preludes.basics:
        let
          returns  = it.returns
          locality = it.locality
          name     = it.name

          selectable = name.strVal
          defsym     = genSym(kind = nskProc, ident = selectable & " (RAW)")
          define     = newProc(name    = defsym,
                               params  = formalize(returns),
                               body    = it.body,
                               pragmas = (quote do: {.cdecl.}))

          pullpush =
            case parseEnum[PreludeBodyKind](it.bodykind.strVal)
            of Override:
              quote do:
                discard
            of Impl:
              quote do:
                discard
      list

    multiargs = block:
      var list = newStmtList()
      for it in preludes.multiargs:
        let
          returns  = it.returns
          locality = it.locality
          argnames = it.argnames
          argtypes = it.argtypes

          (cargs, selectable, identdefs) = setupInputs(
            argtypes, argnames, useArgNames = false)
          defsym = genSym(kind = nskProc, ident = selectable & " (RAW)")
          define = newProc(name    = defsym,
                           params  = formalize(returns, identdefs),
                           body    = it.body,
                           pragmas = (quote do: {.cdecl.}))

          pullpush = case parseEnum[PreludeBodyKind](it.bodykind.strVal)
            of Override:
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
            of Impl:
              # TODO(awr): This requires enconding a method signature against
              # the Obj-C specification. Not impossible but needs some doing
              quote do:
                discard

          submission = quote do:
            `define`
            `pullpush`
            wrapMultiarg `sub`, `returns`, `locality`, `argtypes`, `argnames`
        list &= submission
      list

    bindings = quote do:
      objc_registerClassPair(`subclass`) # No ivars, only method-adding after
      `properties`
      `basics`
      `multiargs`

  result &= bindings

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

# Important utility functions for NSString <-> Nim-side Strings. Not sure
# necessarily if they're part of AppKit or UIKit specifically? Or the Obj-C base
# libraries? We link to them anyway insofar as one imports `appkit` or `uikit`,
# so it shouldn't be a problem:

bindclass NSString:
  + (instancetype) stringWithUTF8String: (cstring) nullTerminatedCString
  + (instancetype) foobar: (cstring) nullTerminatedCString
  @property(readonly) var UTF8String: cstring

proc `$`*(s: NSString): string = $(s.UTF8String)
