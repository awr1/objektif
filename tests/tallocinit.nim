when defined(macosx):
  import
    objektif / objc,
    std / macros

  bindclass NSObject:
    + alloc(): InstanceType
    - init():  InstanceType

  discard NSObject.alloc.init