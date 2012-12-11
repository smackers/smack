import BaseHTTPServer
import SimpleHTTPServer
import json
import subprocess

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


metadata = {
  "Name": "smack",
  "DisplayName": "SMACK",
  "Version": "1.0",
  "Email": "zvonimir@cs.utah.edu",
  "SupportEmail": "zvonimir@cs.utah.edu",
  "TermsOfUseUrl": "http://bitbucket.org/lissa/smack",
  "PrivacyUrl": "http://bitbucket.org/lissa/smack",
  "Institution": "University of Utah",
  "InstitutionUrl": "http://www.cs.utah.edu",
  "InstitutionImageUrl": "http://bytebucket.org/lissa/smack/wiki/SoClogo_red_small.png",
  "MimeType": "text/c",
  "SupportsLanguageSyntax": False,
  "Title": "Static Checker for C/C++ Programs",
  "Description": "SMACK is a tool for statically checking properties of programs written in C/C++. For a given input program, SMACK checks for violations of user-provided assertions. The tool is open-source and integrates into the well-known LLVM compiler infrastructure.",
  "Question": "Are there any assertion violations in this program?",
  "Url": "http://bitbucket.org/lissa/smack",
  "Samples": [
    {
      "Name": "simple",
      "Source": rise_simple
    },
    {
      "Name": "simple_buggy",
      "Source": rise_simple_buggy
    }
  ]
#  "Tutorials": [
#    {
#      "Name": "guide",
#      "Source": "# This is the markdown syntax test.\r\n\r\nA paragraph...\r\n\r\n    first\r\n\r\nThe tutorial also supports TeX maths through mathjax: \r\n\\[\\begin{aligned} \\dot{x} & = \\sigma(y-x) \\\\ \\dot{y} & = \\rho x - y - xz \\\\ \\dot{z} & = -\\beta z + xy \\end{aligned} \\]\r\n",
#      "Samples": [
#        {
#          "Name": "first",
#          "Source": "hello you"
#        }
#      ]
#    }
#  ]
}

class TestHandler(SimpleHTTPServer.SimpleHTTPRequestHandler):
  def do_GET(self):
    print 'get'
    print self.path
    try:
      if self.path.startswith("//metadata"):
        print 'metadata'
        body = json.dumps(metadata)
        self.send_response(200)
        self.send_header('Content-Type', 'text/javascript')
        self.send_header('Content-Length', len(body))
        self.send_header('Expires', '-1')
        self.send_header('Cache-Control', 'no-cache')
        self.send_header('Pragma', 'no-cache')
        self.end_headers()

        self.wfile.write(body)
        self.wfile.flush()
        self.connection.shutdown(1)
        return
      if self.path.endswith("language"):
        print 'language'
        return
      print 'neither metadata nor language'
      return
    except IOError:
      print 'IOError'
      self.send_error(404,'File Not Found: %s' % self.path)

  def do_POST(self):
    print 'post'
    length = int(self.headers.getheader('content-length'))
    print length        
    data_string = self.rfile.read(length)
    print data_string
    data = json.loads(data_string)
    f = open('pero.c', 'w')
    f.write(data["Source"])
    f.close()

    return_code = subprocess.call(["clang", "-c", "-Wall", "-emit-llvm", "-O0", "-I../examples/headers", "pero.c", "-o", "pero.o"])
    if not return_code == 0:
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
      self.send_header('Pragma', 'no-cache')
      self.end_headers()

      self.wfile.write(body)
      self.wfile.flush()
      self.connection.shutdown(1)
      return

    return_code = subprocess.call(["llvm-link", "pero.o", "../examples/headers/smack.o", "-o", "pero"])
    if not return_code == 0:
      smack_response = {
        "Version": "1.0",
        "Outputs": [
          {
            "MimeType": "text/plain",
            "Value": "Link error"
          }
        ]
      }
      body = json.dumps(smack_response)
      self.send_response(200)
      self.send_header('Content-Type', 'text/javascript')
      self.send_header('Content-Length', len(body))
      self.send_header('Expires', '-1')
      self.send_header('Cache-Control', 'no-cache')
      self.send_header('Pragma', 'no-cache')
      self.end_headers()

      self.wfile.write(body)
      self.wfile.flush()
      self.connection.shutdown(1)
      return

    p = subprocess.Popen(["smack", "pero"], stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    smack_string = p.communicate()[0]
    return_code = p.returncode
    if not return_code == 0:
      smack_response = {
        "Version": "1.0",
        "Outputs": [
          {
            "MimeType": "text/plain",
            "Value": "SMACK error"
          }
        ]
      }
      body = json.dumps(smack_response)
      self.send_response(200)
      self.send_header('Content-Type', 'text/javascript')
      self.send_header('Content-Length', len(body))
      self.send_header('Expires', '-1')
      self.send_header('Cache-Control', 'no-cache')
      self.send_header('Pragma', 'no-cache')
      self.end_headers()

      self.wfile.write(body)
      self.wfile.flush()
      self.connection.shutdown(1)
      return


    smack_response = {
      "Version": "1.0",
      "Outputs": [
        {
          "MimeType": "text/plain",
          "Value": smack_string
        }
      ]
    }
    body = json.dumps(smack_response)
    self.send_response(200)
    self.send_header('Content-Type', 'text/javascript')
    self.send_header('Content-Length', len(body))
    self.send_header('Expires', '-1')
    self.send_header('Cache-Control', 'no-cache')
    self.send_header('Pragma', 'no-cache')
    self.end_headers()

    self.wfile.write(body)
    self.wfile.flush()
    self.connection.shutdown(1)


def start_server():
  server_address = ("", PORT)
  server = BaseHTTPServer.HTTPServer(server_address, TestHandler)
  server.serve_forever()


if __name__ == "__main__":
  start_server()

