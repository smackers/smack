import BaseHTTPServer
import SimpleHTTPServer
import json
import subprocess
import os, time, re
import random

PORT = 8080
version = "1.4.4"
rise_simple = """#include "smack.h"
//__SMACK_nondet() : Is used to permit assigned memory to have unconstrained values
//__SMACK_assume(): Is used to enforce constraints on specified regions of memory
//__SMACK_assert(): Is used to prove some assertions on values in the program. Assertions may contain unconstrained values.
int main() {
  int x = __SMACK_nondet();
  int n = __SMACK_nondet();
  __SMACK_assume(n>0);
  __SMACK_assert(x+n > x);
  return 0;
}"""

rise_simple_buggy = """#include "smack.h"
//__SMACK_nondet() : Is used to permit assigned memory to have unconstrained values
//__SMACK_assume(): Is used to enforce constraints on specified regions of memory
//__SMACK_assert(): Is used to prove some assertions on values in the program. Assertions may contain unconstrained values
int main() {
  int x = __SMACK_nondet();
  int n = __SMACK_nondet();
  __SMACK_assume(n>=0);
  __SMACK_assert(x+n > x);
  return 0;
}"""

func_ptr_fail ="""#include "smack.h"
//As demonstrated here, we can prove the correctness of functions for the entire range of input values
int incr(int x) {
  return ++x;
}

int decr(int x) {
  return --x;
}

int main(void) {
  int (*fp)(int);
  int x = __SMACK_nondet(), y = __SMACK_nondet(), old_x = x;

  if (y > 0) {
    fp = incr;
  } else {
    fp = decr;
  }
  x = fp(x);

  __SMACK_assert(x == old_x-1 || x == old_x+1);
  return 0;
}"""

loop = """#include "smack.h"
//By specifying a sufficient loop unroll factor, we can reason about loops.
//Specify the loop unroll factor here with the syntax @LU:<unroll count>@ E.g: @LU:8@
void initDescArray(int number[], int size)
{
  int i;
 for(i=size-1;i>=0;i--)
    number[i]=i;

}

int main()
{
  int num[6], size = 6;
  int i = __SMACK_nondet();
  initDescArray(num,size);
  if(i >= 1 && i < 6)
    __SMACK_assert(num[i] > num[i-1]);
}"""


complicated_function = """#include "smack.h"
//We can prove properties of return values of procedures for all possible input parameters
int foo(int x, int y) {
  int a;

  if (x < y) {
    a = 3;
  } else if (x > y) {
    a = 2;
  } else {
    a = 1;
  }
  a++;
  if (a > 2) {
    a--;
    if (x < 0) {
      a++; x++;
    } else {
      a--; x--;
    }
  } else {
    if (y < 0) {
      a--; y--;
    } else {
      a++; y++;
    }
  }
  if (x == a && y == a) {
    a--;
  }
  return a;
}

int main(void) {
  int b;

  b = foo(__SMACK_nondet(), __SMACK_nondet());
  __SMACK_assert(b != 0);
  return 0;
}"""

limit_multiply="""#include "smack.h"
//Though support by the theorem prover is limited for multiplication, we can solve some equations
int main(void) {
  int x, y, z, a, b;

  x = 4;
  y = 3;
  z = 19;
  a = __SMACK_nondet();
  b = __SMACK_nondet();
  if(a>=0 && b>=0)
        __SMACK_assert(z != (a*x+b*y));
  return 0;
}"""

structcast = """#include <stdio.h>
#include <stdlib.h>
#include "smack.h"
//Memory is modeled to match the C specification
typedef struct {
  int a;
  int b;
} S1;

typedef struct {
  int x;
} S2;

int main(void) {
  S1 s1;
  S2* p2 = (S2*)(&s1);

  s1.a = 3;
  p2->x = 4;

  __SMACK_assert(s1.a == 4);
  return 0;
}"""


tutorialsource = """SMACK is a SMACK is a tool for statically checking properties of programs written in C/C++. 
		For a given input program, SMACK checks for violations of user-provided assertions. 
		The tool is open-source and integrates into the well-known LLVM compiler infrastructure.\r\n 
		There are 3 types of annotations that SMACK allows the user to specify. They are the assert, assume and nondet statements.\r\n
		Assert: Allows the user to specify a predicate on the variables in scope. SMACK statically checks the assertion in this 
		program location. The predicate P can be specified in an assert in the syntax __SMACK_assert(P)  \r\n
		Assume: Assume statement allows the user to specify the assumptions of the program from the point of specification. If the 
		assumption is denoted by A, __SMACK_assume(A) is the syntax for specifying it. Eg: __SMACK_assume(n > 0)
		Nondet: Allows the user to specify a "random" value. This is specified by __SMACK_nondet(). The statement returns a 
		nondeterministic type safe value."""
metadata = {
	"Name": "smack",
	"DisplayName": "SMACK",
	"Version": version,
	"Email": "smack-dev@googlegroups.com",
	"SupportEmail": "smack-dev@googlegroups.com",
	"TermsOfUseUrl": "https://github.com/smackers/smack/",
	"PrivacyUrl": "https://github.com/smackers/smack/",
	"Institution": "University of Utah and IMDEA Software Institute",
	"InstitutionUrl": "https://github.com/smackers/smack/",
	"InstitutionImageUrl": "https://dl.dropboxusercontent.com/u/93242277/smack-logo.png",
	"MimeType": "text/x-c",
	"SupportsLanguageSyntax": True,
	"Title": "Verifier for C/C++ Programs",
	"Description": "At its core, SMACK is a translator from the LLVM compiler's popular intermediate representation (IR) into the Boogie intermediate verification language (IVL). Sourcing LLVM IR exploits an increasing number of compiler frontends, optimizations, and analyses. Targeting Boogie exploits a canonical platform which simplifies the implementation of algorithms for verification, model checking, and abstract interpretation. The main purpose of SMACK is to decouple the implementations of verification algorithms from the details of source languages, and enable rapid prototyping on production code.",
	"Question": "Are there any assertion violations in this program?",
	"Url": "https://github.com/smackers/smack/",
	"Samples": [
	{
		"Name": "simple proof",
		"Source": rise_simple
	},
	{
		"Name": "simple buggy example",
		"Source": rise_simple_buggy
	},
	{
		"Name": "function pointers",
		"Source": func_ptr_fail
	},
	{
		"Name": "loops and arrays",
		"Source": loop
	},
	{
		"Name": "procedure summaries",
		"Source": complicated_function
	},
	{
		"Name": "solving equations",
		"Source": limit_multiply
	},
	{
		"Name": "structures",
		"Source": structcast
	}
	]
}

class TestHandler(SimpleHTTPServer.SimpleHTTPRequestHandler):
	def do_GET(self):
		try:
			if self.path.startswith("/metadata"):
				body = json.dumps(metadata)
				self.send_response(200)
				self.send_header('Content-Type', 'text/javascript')
				self.send_header('Content-Length', len(body))
				self.send_header('Expires', '-1')
				self.send_header('Cache-Control', 'no-cache')
				self.send_header('Cache-Control', 'no-store')
				self.send_header('Cache-Control', 'must-revalidate')
				self.send_header('Cache-Control', 'max-age=0')
				self.send_header('Pragma', 'no-cache')
				self.end_headers()
				self.wfile.write(body)
				self.wfile.flush()
				self.connection.shutdown(1)
				return
			if self.path.endswith("language"):
				return
			return
		except IOError:
			print 'IOError'
			self.send_error(404,'File Not Found: %s' % self.path)

	def do_POST(self):
		length = int(self.headers.getheader('content-length'))      
		data_string = self.rfile.read(length)
		data = json.loads(data_string)

		f = open("rollingcount",'r')
		x = int(f.read())+1
		filename = 'input_'+str(x)
		f.close()
		f = open("rollingcount",'w')
		f.write(str(x))
		f.close()

		f = open(filename+'.c', 'w')
		f.write(data["Source"])
		f.close()
		regulex = re.match(r".*@LU:(?P<lu>\d+)@.*", data["Source"],re.DOTALL)
		if(regulex):
			lucount = regulex.groupdict()["lu"]
		else:
			lucount = '2'
		

		f = open('logs','a')

		p = subprocess.Popen(["timeout","10s",'smackverify.py', '--unroll', lucount, filename + '.c', '-o', filename +'.bpl'], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
		smack_string = p.communicate()
		return_code = p.returncode
		if not return_code == 0:
			if return_code == 124:
				resp = "Program is taking unusually long to verify. Request timed out."
                        	smack_response = {
                                	"Version": version,
	                                "Outputs": [
        	                        {
                	                        "MimeType": "text/plain",
                        	                "Value": resp
                                	}
                                	]
                        	}
				f.write(self.client_address[0]+"--"+filename+".c--"+"Timed Out\n")
				f.close()
			else:
				output = smack_string[0].replace(filename+'.c', 'input.c')
				output = output.split(' ')
				error = []
				smack = ''
				for i in range(len(output)):
					if(output[i] == "error:" or output[i] == "warning:"):
						error.append(i)
				for i in range(len(error)):
					t = output[error[i]-1].split(':')
					flag =1
					if(output[error[i]-1] == 'fatal'):
						flag = 0
					if(i < len(error)-1 and flag):
						m = output[error[i]].split(':')
						j = error[i]+1
						while 1:
							if('\n' in output[j]):
								break
							j = j+1
						haha = output[j].find('\n')
						output[j] = output[j][0:haha]
						p = output[error[i]+1:j+1]
						we = " "
						p = we.join(p)
						if(len(t) < 3 or len(m) < 1):
							smack = smack+" SMACK Error\r\n"
						else:
							smack = smack+"input.c("+t[1]+","+t[2]+") : "+m[0]+" "+str(i)+": "+p+"\r\n"
					elif(i == len(error)-1 and flag):
						m = output[error[i]].split(':')
                       	                        j = error[i]+1
                               	                while 1:
                                       	                if('\n' in output[j]):
                                               	                break
							j = j+ 1
						haha = output[j].find('\n')
                                                output[j] = output[j][0:haha]
                                                p = output[error[i]+1:j+1]
       	                                        we = " "
               	                                p = we.join(p)
						if(len(t) >= 3 or len(m) >= 1):
	                       	                        smack = smack+"input.c("+t[1]+","+t[2]+") : "+m[0]+" "+str(i)+": "+p+"\r\n"
						else:
							smack = smack+" SMACK Error\r\n"
				if(smack == ''):
					smack = "SMACK Error"
				smack_response = {
					"Version": version,
					"Outputs": [
					{
						"MimeType": "text/plain",
						"Value": smack
					}
					]
				}
				f.write(self.client_address[0]+"--"+filename+".c--"+"SMACK Error\n")
				f.close()
		else:  
			outp = smack_string[0].replace(filename+'.c', 'input.c')
			output = outp.split(' ')
                        output = [i for i in output if '$' not in i]
			for i in range(len(output)):
				if '):' in output[i]:
					output[i]=output[i][0:len(output[i])-1]+"\n"                
                        t=" "
                        smack = t.join(output) 
			g = open(filename+".output",'w')
                        g.write(smack)
                        g.close()
			f.write(self.client_address[0]+"--"+filename+".c--"+"Output\n")
			f.close()
			if('not hold' in outp):
				temp = smack.split('\n')
				temp = [w for w in temp if w != '']
				response = temp[0]+"\r\n"
				flag = 1
				cnt = 0
				for i in range(len(temp)):
					if('input' in temp[i] and flag):
						response = response+temp[i]+" : error main: This assertion might not hold\r\n"
						flag = 0
					elif('input' in temp[i] and flag == 0): 
						response = response+temp[i]+" : Trace Element: Error trace["+str(cnt)+"]\r\n"
						cnt = cnt +1
				response = response + temp[len(temp)-1]
					
				smack_response = {
					"Version": version,
					"Outputs": [
					{
						"MimeType": "text/plain",
						"Value": response
					}
					]
				}
			else:
				 smack_response = {
                                        "Version": version,
                                        "Outputs": [
                                        {
                                                "MimeType": "text/plain",
                                                "Value": smack
                                        }
                                        ]
                                }

			f.close()
		body = json.dumps(smack_response)
		self.send_response(200)
		self.send_header('Content-Type', 'text/javascript')
		self.send_header('Content-Length', len(body))
		self.send_header('Expires', '-1')
		self.send_header('Cache-Control', 'no-cache')
		self.send_header('Cache-Control', 'no-store')
		self.send_header('Cache-Control', 'must-revalidate')
		self.send_header('Cache-Control', 'max-age=0')
		self.send_header('Pragma', 'no-cache')
		self.end_headers()
		self.wfile.write(body)
		self.wfile.flush()
		os.system("rm "+filename+".b*")
		self.connection.shutdown(1)
		return

def start_server():
	server_address = ("", PORT)
	server = BaseHTTPServer.HTTPServer(server_address, TestHandler)
	server.serve_forever()

if __name__ == "__main__":
	start_server()

