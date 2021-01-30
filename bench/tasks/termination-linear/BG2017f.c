// Source: Amir M. Ben-Amram, Samir Genaim, "On Multiphase-Linear
// Ranking Functions", CAV 2017.


extern int __VERIFIER_nondet_int(void);

int main(int argc, char* argv[]) {
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  // avoid overflow
  if (x > 1000 || y > 1000) return 0;

  // The bound 2^By >= x is omitted, so that the termination argument
  // must apply for all B.
  while (x >= 1 && y >= 1 && x >= y) {
    x = 2 * x;
    y = 3 * y;
  }

  return 0;
}
