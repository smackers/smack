import BaseHTTPServer
import SimpleHTTPServer
import json
import subprocess
import os, time
import random

PORT = 8080

rise_simple = """#include \"smack.h\"

int main(void) {
  int x, y, z;

  x = 10;
  y = 20;
  z = x + y;
  __SMACK_assert(z == 30);
  return 0;
}"""

rise_simple_buggy = """#include \"smack.h\"

int main(void) {
  int x, y, z;

  x = 10;
  y = 20;
  z = x + y;
  __SMACK_assert(z != 30);
  return 0;
}"""

func_ptr_fail ="""#include "smack.h"

int incr(int x) {
  return ++x;
}

int decr(int x) {
  return --x;
}

int main(void) {
  int (*fp)(int);
  int x = 1, y = 1;

  if (y > 0) {
    fp = incr;
  } else {
    fp = decr;
  }
  x = fp(x);

  __SMACK_assert(x == 0 || x == 1);
  return 0;
}"""

loop = """#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

#define MAXSIZE 10

int x;

int main() {
  int i = 0;

  x = 0;

  for (i = 0; i < MAXSIZE; i++) {
    x = i;
  }
  __SMACK_assert(x == MAXSIZE - 1);
  return 0;
}"""

nondet = """#include "smack.h"

int main(void) {
  int x = 1;

  if (__SMACK_nondet()) {
    x++;
  } else {
    x--;
  }

  __SMACK_assert(x == 0 || x == 2);
  return 0;
}"""

nondet2 = """#include "smack.h"

int main() {
  int x = __SMACK_nondet();

  if (x == 0) {
    goto ERROR;
  } else {
    goto out;
  }

  out:
    return x+1;
  ERROR:
    return 0;
}"""

assume_example = """#include "smack.h"

int main() {
  int x = __SMACK_nondet();
  int n;
  __SMACK_assume(n>0);
  __SMACK_assert(x+n > x);
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
	"Version": "1.0",
	"Email": "zvonimir@cs.utah.edu",
	"SupportEmail": "zvonimir@cs.utah.edu",
	"TermsOfUseUrl": "https://github.com/smackers/smack",
	"PrivacyUrl": "https://github.com/smackers/smack",
	"Institution": "University of Utah",
	"InstitutionUrl": "http://www.cs.utah.edu",
	"InstitutionImageUrl": "https://dl.dropboxusercontent.com/u/93242277/logos.jpg",
	"MimeType": "text/c",
	"SupportsLanguageSyntax": False,
	"Title": "Static Checker for C/C++ Programs",
	"Description": "SMACK is a tool for statically checking properties of programs written in C/C++. For a given input program, SMACK checks for violations of user-provided  			assertions. The tool is open-source and integrates into the well-known LLVM compiler infrastructure.",
	"Question": "Are there any assertion violations in this program?",
	"Url": "https://github.com/smackers/smack",
	"Samples": [
	{
		"Name": "Simple",
		"Source": rise_simple
	},
	{
		"Name": "Simple_buggy",
		"Source": rise_simple_buggy
	},
	{
		"Name": "Func. Ptr_buggy",
		"Source": func_ptr_fail
	},
	{
		"Name": "Loop assert",
		"Source": loop
	},
	{
		"Name": "Simple Theorem",
		"Source": assume_example
	}
	],
	"Tutorials": [
	{
		"Name": "guide",
		"Source": tutorialsource,
		"Samples": [
		{
			"Name": "Sample Assert",
			"Source": rise_simple
		},
		{
                        "Name": "Sample nondet",
                        "Source": nondet2
                },
		{
			"Name": "Sample Assume",
			"Source": assume_example
		}
		]
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
		#x = time.localtime()
		random.seed()
		x = str(random.random()).split('.')[1]
		#filename = 'pero'+str(x.tm_hour)+str(x.tm_min)+str(x.tm_sec)
		filename = 'pero'+x
		f = open(filename+'.c', 'w')
		f.write(data["Source"])
		f.close()
		f = open('logs','a')
		q = subprocess.call(["clang", "-c", "-Wall", "-emit-llvm", "-O0", "-I../include/smack", filename+".c", "-o", filename+".bc"])
		if not q == 0:
			smack_response = {
				"Version": "1.0",
				"Outputs": [
				{
					"MimeType": "text/plain",
					"Value": "Compile error"
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
			f.write(self.client_address[0]+"--"+filename+".c--"+"Compiler Error\n")
			f.close()
			os.system("rm "+filename+".b*")
			self.connection.shutdown(1)
			return
		#p = subprocess.Popen(["timeout","60","smack-verif.py", filename+".bc", "-o", filename+".bpl"], stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
		p = subprocess.Popen(['smack-verify.py', filename + '.bc', '-o', filename +'.bpl'], stdout=subprocess.PIPE)
		smack_string = p.communicate()[0]
		return_code = p.returncode
		if not return_code == 0:
			if return_code == 31744:
                        	smack_response = {
                                	"Version": "1.0",
	                                "Outputs": [
        	                        {
                	                        "MimeType": "text/plain",
                        	                "Value": "Program is taking unusually long to verify. Request timed out."
                                	}
                                	]
                        	}
				f.write(self.client_address[0]+"--"+filename+".c--"+"Timed Out\n")
				f.close()
			else:
				smack_response = {
					"Version": "1.0",
					"Outputs": [
					{
						"MimeType": "text/plain",
						"Value": "SMACK error"
					}
					]
				}
				f.write(self.client_address[0]+"--"+filename+".c--"+"SMACK Error\n")
				f.close()
		else:  
			output = smack_string.split(' ')
                        output = [i for i in output if '$' not in i]
			for i in range(len(output)):
				if '):' in output[i]:
					output[i]=output[i][0:len(output[i])-1]+"\n"
                        t=" "
                        smack_string = t.join(output) 
			g = open(filename+".output",'w')
                        g.write(smack_string)
                        g.close()
			f.write(self.client_address[0]+"--"+filename+".c--"+"Output\n")
			f.close()
			smack_string = smack_string+ "\nRefer execution trace line numbers in this Boogie File:\n"
			smack_string = smack_string+subprocess.check_output(["cat", "-n", filename+".bpl"])
			smack_response = {
				"Version": "1.0",
				"Outputs": [
				{
					"MimeType": "text/plain",
					"Value": smack_string
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

