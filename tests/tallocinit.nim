when defined(macosx):
  import objektif / objc

  bindclass NSObject:
    + alloc(): InstanceType
    - init():  InstanceType

  discard NSObject.alloc.init