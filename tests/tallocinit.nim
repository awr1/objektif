when defined(macosx):
  import
    objektif / objc,
    std / macros

  bindclass NSObject:
    + alloc(): int
    - init():  InstanceType

let x = NSObject.alloc.init