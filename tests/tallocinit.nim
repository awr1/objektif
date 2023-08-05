when defined(macosx):
  import
    objektif / objc,
    std / macros

  bindclass NSObject:
    + alloc(): int
    - init():  InstanceType

  discard NSObject.alloc