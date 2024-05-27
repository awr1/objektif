import
  objektif / runtime,
  zero_functional,
  std / macros,
  std / typetraits,
  std / tables

type NSObject* = ptr object of id

# TODO(awr): std / macrocache approach for caching selectors?
template classify*(`type`: typedesc): id =
  var cached {.global.}: id
  if cached == nil: cached = cast[id](objc_getClass($`type`))
  cached

template selectify*(name: static[string]): SEL =
  let cached {.global.} = sel_registerName(name)
  cached

template identify*[T](obj: T or typedesc[T]): id =
  when obj is typedesc[T]: classify(obj)
  else:                    cast[id](obj)

type
  PropertyAttrib* = enum
    readwrite, readonly, dynamic, strong, weak, copy, assign, retain, nonatomic,
    getter, setter # Refers to a CUSTOM getter/setter
  MessageLocality* = enum
    Metaclass, Instance
  RuntimeSender* = enum
    Void, PassType, Identifier, Integer, Float, Super, StructReg, StructPtr

func `[]`*(node:      NimNode;
           i:         int or BackwardsIndex;
           expected:  set[NimNodeKind];
           sublength: int = -1): NimNode =
  result = node[i]
  expectKind result, expected
  if sublength > -1:
    expectLen result, sublength

const AttribEncoding* = {
  readonly:  "R",
  copy:      "C",
  retain:    "&",
  nonatomic: "N",
  getter:    "G",
  setter:    "S",
  dynamic:   "D",
  weak:      "W"}.toTable

func toSenderKind*(desc: typedesc): RuntimeSender =
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

macro encodeObject(ctordesc: typed): NimNode =
  # MUST be an constructor from a typedesc! Using `getTypeImpl` permits us to
  # do immediate generic substitution.
  let
    impl    = ctordesc.getTypeImpl[1]
    reclist = impl[2, {nnkRecList}]

  # The Obj-C runtime has a special case for bitfields. The likelihood that
  # anyone at Apple is seriously depending on one of C's most UB-ass features in
  # the Obj-C system frameworks is slim-to-none. `getTypeImpl` does not actually
  # emit bitfield information, we would have to defer to `getTypeInst` and match
  # by the field name and honestly IDRC enough to do that at this time.
  reclist.zfun:
    map:
      (name: it[0], `type`: it[1])
      quote do: encodeType(it.`type`)
    reduce:
      quote do: a & b

macro encodeProc(desc: typed): NimNode =
  let
    init    = desc.getType[0, {nnkBracketExpr}]
    formals =
      if init[0].eqIdent("typedesc"): init[1]
      else:                           init

  formals.zfun:
    map:
      quote do: encodeType(it, false)
    reduce:
      quote do: a & b

func encodeType*(desc: typedesc; first: static[bool] = true): string =
  when desc is SEL:        ":"
  elif desc is Class:      "#"
  elif desc is id:         "@"
  elif desc is NSObject:   "@"
  elif desc is cint:       "i"
  elif desc is cuint:      "I"
  elif desc is clong:      "l"
  elif desc is culong:     "L"
  elif desc is clonglong:  "q"
  elif desc is culonglong: "Q"
  elif desc is cfloat:     "f"
  elif desc is cdouble:    "d"
  elif desc is cchar:      "c"
  elif desc is cuchar:     "C"
  elif desc is cstring:    "*"
  elif desc is pointer:    "^v"
  elif desc is ptr:        "^" & desc.pointerBase.encodeType(false)
  elif desc is array:
    "[" & desc.len & desc.elementType.encodeType(false) & "]"
  elif desc is object:
    "{" & desc.name & "?=" & encodeObject(desc()) & "}"
  elif desc is (proc):
    when first:
      ""
    else:
      "?"
  else:
    ""
