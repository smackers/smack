#include "smack.h"

int main() {
  int a = 2;
  
  switch(a){
    case 0:
      a++;
    case 1:
      a--;
    default:
      a *= 2;
  }
    
  return a;
}
