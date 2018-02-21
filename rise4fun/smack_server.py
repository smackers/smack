#
# This file is distributed under the MIT License. See LICENSE for details.
#
import BaseHTTPServer
import SimpleHTTPServer
import json
import subprocess
import os, time, re
import random

PORT = 8080
version = "1.4.4"
rise_simple = """#include "smack.h"
//__VERIFIER_nondet_int() : Is used to permit assigned memory to have unconstrained values
//assume(): Is used to enforce constraints on specified regions of memory
//assert(): Is used to prove some assertions on values in the program. Assertions may contain unconstrained values.
int main() {
  int x = __VERIFIER_nondet_int();
  int n = __VERIFIER_nondet_int();
  assume(n>0);
  assert(x+n > x);
  return 0;
}"""

rise_simple_buggy = """#include "smack.h"
//__VERIFIER_nondet() : Is used to permit assigned memory to have unconstrained values
//assume(): Is used to enforce constraints on specified regions of memory
//assert(): Is used to prove some assertions on values in the program. Assertions may contain unconstrained values
int main() {
  int x = __VERIFIER_nondet_int();
  int n = __VERIFIER_nondet_int();
  assume(n>=0);
  assert(x+n > x);
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
  int x = __VERIFIER_nondet_int(), y = __VERIFIER_nondet_int(), old_x = x;

  if (y > 0) {
    fp = incr;
  } else {
    fp = decr;
  }
  x = fp(x);

  assert(x == old_x-1 || x == old_x+1);
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
  int i = __VERIFIER_nondet_int();
  initDescArray(num,size);
  if(i >= 1 && i < 6)
    assert(num[i] > num[i-1]);
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

  b = foo(__VERIFIER_nondet_int(), __VERIFIER_nondet_int());
  assert(b != 0);
  return 0;
}"""

limit_multiply="""#include "smack.h"
//Though support by the theorem prover is limited for multiplication, we can solve some equations
int main(void) {
  int x, y, z, a, b;

  x = 4;
  y = 3;
  z = 19;
  a = __VERIFIER_nondet_int();
  b = __VERIFIER_nondet_int();
  if(a>=0 && b>=0)
        assert(z != (a*x+b*y));
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

  assert(s1.a == 4);
  return 0;
}"""


tutorialsource = """SMACK is a SMACK is a tool for statically checking properties of programs written in C/C++. 
		For a given input program, SMACK checks for violations of user-provided assertions. 
		The tool is open-source and integrates into the well-known LLVM compiler infrastructure.\r\n 
		There are 3 types of annotations that SMACK allows the user to specify. They are the assert, assume and nondet statements.\r\n
		Assert: Allows the user to specify a predicate on the variables in scope. SMACK statically checks the assertion in this 
		program location. The predicate P can be specified in an assert in the syntax assert(P)  \r\n
		Assume: Assume statement allows the user to specify the assumptions of the program from the point of specification. If the 
		assumption is denoted by A, assume(A) is the syntax for specifying it. Eg: assume(n > 0)
		Nondet: Allows the user to specify a "random" value. This is specified by __VERIFIER_nondet(). The statement returns a 
		nondeterministic type safe value."""
metadata = {
	"Name": "smack",
	"DisplayName": "SMACK",
	"Version": version,
	"Email": "smack-dev@googlegroups.com",
	"SupportEmail": "smack-dev@googlegroups.com",
	"TermsOfUseUrl": "https://github.com/smackers/smack/",
	"PrivacyUrl": "https://github.com/smackers/smack/",
	"Institution": "University of Utah",
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
			print ('IOError')
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

		p = subprocess.Popen(["timeout", "10s", '/uusoc/exports/scratch/rise4fun/smack/install/bin/smack', '--time-limit', '10', '--unroll', lucount, filename + '.c', '-bpl',
							  filename + '.bpl'], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
		smack_string = p.communicate()
		smack_response = ""
		return_code = p.returncode
		#check that smack ran successfully.
		if not return_code == 0:
			output = smack_string[0].replace(filename + '.c', 'input.c')
			print("Output contained timeout code: " + str('timed out' in output))
			output = output.split('\n')
			if "SMACK timed out." in smack_string[1]:
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
				error = []
				smack = ''
				for i in range(len(output)):
					#Check if an error's trace is avaliable in the smack output.
					if "Trace" in output[i] and "input.c" in output[i]:
						line_number = output[i][output[i].index("input.c("):output[i].index(",")]
						trace = output[i][output[i].index(":") + 1:]
						smack += line_number + "): error 1: " + trace + "\r\n"
					#Check if an assert failed while running smack.
					if "(ASSERTION FAILS" in output[i]: #we have an assertion that is failing, so report it.
						line_number = output[i+1][output[i+1].index("("):output[i+1].index(",")]
						smack = "input.c" + line_number + "): error 1: Assertion Failed!\r\n" + smack
						#Grab each individual trace from the failed assertion and add to smack string
					if "error: " in output[i]: #check if any syntax errors exist.
						line_number = "(" + output[i][output[i].index(":") + 1:output[i].index(" ") - 1] + ")" #grab the line and column number from the error.
						line_number = line_number[:line_number.index(":")] + ")"
						error = output[i][output[i].index("error: "):] #grab the error
						error = error.replace("error:", "error 2:")
						smack += "input.c " + line_number + ": " + error + "\r\n"
				if smack == '': #Something happened while trying to read the input. Let Rise4Fun know we couldn't process the file.
					smack = "input.c(0): error 3: SMACK encountered an error and was unable to process the input file.\r\n"
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
		smack_response = {
			"Version": version,
			"Outputs": [
				{
					"MimeType": "text/plain",
					"Value": smack
				}
			]
		}
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
		os.system("rm "+filename+".c*")
		self.connection.shutdown(1)
		return

def start_server():
	server_address = ("", PORT)
	server = BaseHTTPServer.HTTPServer(server_address, TestHandler)
	server.serve_forever()

if __name__ == "__main__":
	start_server()

