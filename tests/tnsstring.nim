when defined(macosx):
  import objektif / objc

  let
    nimstr = "こんにちは"
    objstr = NSString => (stringWithUTF8String: nimstr.cstring)

  assert $objstr == nimstr
