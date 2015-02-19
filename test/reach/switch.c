#include "smack.h"

int main() {
  int a = 1;
  
  switch(a){
    case 0:
      a++;
      break;
    case 1:
      a--;
      break;
    default:
      a = a*2;
      break;
  }
    
  return a;
}
