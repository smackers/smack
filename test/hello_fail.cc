#include <smack.h>
#include <iostream>
 
int main()
{
    std::cout << "Hello, world!" << std::endl;
    __SMACK_assert(false);
    return 0;
}
