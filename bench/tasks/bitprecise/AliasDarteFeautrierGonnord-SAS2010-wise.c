extern int __VERIFIER_nondet_int();
extern void __VERIFIER_assume(int);
int nondet_signed_int() {
  int r = __VERIFIER_nondet_int();
  __VERIFIER_assume ((-0x7fffffff - 1) <= r && r <= 0x7fffffff);
  return r;
}
signed int main()
{
  signed int x;
  signed int y;
  x = nondet_signed_int();
  y = nondet_signed_int();
  if(x >= 0 && y >= 0)
    do
    {
      while(!(!(x - y < (-0x7fffffff - 1) || 0x7fffffff < x - y)));
      while(!(!(!(x - y > 2)) || (!(x - y > 2))));
      if(!(x + -y >= 3) && !(y + -x >= 3))
        break;
      if(!(x >= y))
      {
        while(!(!(x + 1 < (-0x7fffffff - 1) || 0x7fffffff < x + 1)));
        x = x + 1;
      }
      else
      {
        while(!(!(y + 1 < (-0x7fffffff - 1) || 0x7fffffff < y + 1)));
        y = y + 1;
      }
    }
    while((char)1);
  return 0;
}
