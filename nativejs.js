function fibJS(n) {
  if (n == 1) {
    return 1
  } else if (n == 2) {
    return 2
  } else {
    return (fibJS(n-2) + fibJS(n-1))
  }
}