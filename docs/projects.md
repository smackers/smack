## Projects


Here is an incomplete list of project ideas for extending SMACK in
various directions. If any of these projects are of interest to you,
then email us and we can talk more.

1. Verify an application or piece of code of your choice with SMACK.
This might be a good project for somebody knowledgeable about OS and
low-level programming since SMACK currently mainly supports C.
Embedded and OS codes would be good targets, or C projects in general. 

2. Currently SMACK supports C and a little bit of C++. Since it is
built on top of LLVM, any programming language supported by LLVM could
be targeted by SMACK, at least in theory. So pick your favorite language
(e.g., C++, Objective-C, Swift, Fortran) supported by LLVM and try to extend
SMACK to support it. For example, if you are an iPhone developer, you
might have some expertise in Objective-C and/or Swift. And you could
even base the project around verifying your own iPhone app's code.

3. Try to use and extend SMACK to verify some of the example from the
annual [VerifyThis Competition](http://verifythis.ethz.ch).
SMACK already has a rudimentary support for writing program contracts,
but that would probably have to be extended.

4. Extend SMACK with support for various libraries, such as string.h.
Or maybe some of C++ standard libraries.

5. There are projects one could work on related to combining software
verification with machine learning, data mining, and visualization.
For example, there are opportunities to study automatic parameter tuning of
algorithms (using ML techniques), and try to apply those on some of the
software verification benchmarks we have. It would also be great and
useful to develop a nice browser-based IDE for SMACK.

6. Implement support for weak memory models in SMACK. There are related
research papers that would have to be studied first.

7. Parallelize SMACK or run it in a cloud infrastructure.

