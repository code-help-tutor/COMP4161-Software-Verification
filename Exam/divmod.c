WeChat: cstutorcs
QQ: 749389476
Email: tutorcs@163.com
unsigned divmod(unsigned n, unsigned m, unsigned domod) {
  unsigned d = 0;
  while(n >= m) {
    n -= m;
    d++;
  }
  if (domod) {
    return n;
  } else {
    return d;
  }
}

unsigned even(unsigned n){
  return (divmod(n,2,1) == 0);
}
