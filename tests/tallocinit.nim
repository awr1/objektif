when defined(macosx):
  import objektif / objc

  type
    NSInteger      = clong
    NSTimeInterval = cdouble
    NSArray[T]     = ptr object of NSObject
    NSRunLoopMode  = NSString

  bindclass NSObject:
    + (instancetype) alloc
    - (instancetype) init
    + (void) setVersion: (NSInteger) aVersion
    - (void) performSelector: (SEL)                        aSelector,
             withObject:      (id)                         anArgument,
             afterDelay:      (NSTimeInterval)             delay,
             inModes:         (ptr NSArray[NSRunLoopMode]) modes
    @property(readonly) var classForArchiver: Class

  discard NSObject.alloc.init
  NSObject => (setVersion: 1.clong)