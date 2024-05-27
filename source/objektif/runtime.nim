## Ground-level types and bindings to the Objective-C runtime interface.

{.passL: "-framework Foundation".}
{.passL: "-lobjc".}

type
  SEL*      = distinct pointer
  Class*    = distinct pointer
  IMP*      = distinct pointer
  Method*   = distinct pointer
  Protocol* = distinct pointer
  Ivar*     = distinct pointer

  id*           {.pure, inheritable.} = ptr object
  instancetype* {.final.}             = ptr object of id
  Alias*[T]                           = T

{.push cdecl, importc, dynlib: "libobjc.A.dylib".}
proc sel_registerName*(name: cstring): SEL

{.push varargs.}
proc objc_msgSend*      (self: id; name: SEL): id
proc objc_msgSend_fpret*(self: id; name: SEL): cdouble
proc objc_msgSend_stret*(outp: pointer; self: id; op: SEL)
{.pop.}

proc method_getTypeEncoding*(meth: Method): cstring
proc object_getClass*       (obj:  id):     Class

proc class_getClassMethod*(class: Class; name: SEL): Method
proc objc_getClass*       (name: cstring):           Class

proc class_addMethod*(
  class: Class;
  name:  SEL;
  impl:  IMP;
  types: cstring): bool
proc objc_allocateClassPair*(
  class:      Class;
  name:       cstring;
  extraBytes: csize_t): Class
proc objc_registerClassPair*(class: Class)

proc objc_getProtocol*        (name: cstring):                 Protocol
proc class_addProtocol*       (class: Class; proto: Protocol): bool
proc class_conformsToProtocol*(class: Class; proto: Protocol): bool

proc class_addIvar*(
  class:     Class;
  name:      cstring;
  size:      csize_t;
  alignment: uint8;
  types:     cstring): bool
proc class_getInstanceVariable*(obj: id; name: cstring): Ivar
proc ivar_getOffset*           (ivar: Ivar):             int
proc object_getIvar*           (obj: id; ivar: Ivar):    id
proc object_setIvar*           (obj: id; ivar: Ivar; value: id)
{.pop.}