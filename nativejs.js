function fibJS(n) {
  if (n == 1) {
    return 1
  } else if (n == 2) {
    return 2
  } else {
    return (fibJS(n-2) + fibJS(n-1))
  }
}

function numbers(min, max) {
	var res = []
	for (var i = min; i <= max; i++) {
		res.push(i)
	}
  return res
}

function sum(a) {
	return a.reduce(function(a, b) { return a + b; }, 0)
}

// Copied and renamed from http://stackoverflow.com/a/12287599/682376
function primes(max) {
    var sieve = [], i, j, primes = [];
    for (i = 2; i <= max; ++i) {
        if (!sieve[i]) {
            // i has not been marked -- it is prime
            primes.push(i);
            for (j = i << 1; j <= max; j += i) {
                sieve[j] = true;
            }
        }
    }
    return primes;
}