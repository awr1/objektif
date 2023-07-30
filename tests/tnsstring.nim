when defined(macosx):
  import objektiv / objc

  let
    nimstr = "こんにちは"
    objstr = NSString => (stringWithUTF8String: nimstr.cstring)

  assert $objstr == nimstr
