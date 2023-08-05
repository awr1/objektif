when defined(macosx):
  import objektif / objc

  bindclass NSObject:
    + (instancetype) alloc
    - (instancetype) init
    + (void) setVersion: (NSInteger) aVersion
    - (void) performSelector: (SEL)                        aSelector,
             withObject:      (id)                         anArgument,
             afterDelay:      (NSTimeInterval)             delay,
             inModes:         (ptr NSArray[NSRunLoopMode]) modes =
      performSelector()

  discard NSObject.alloc.init