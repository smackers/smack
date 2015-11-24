import re

def beforeTokenReplace(inputStr):
  inputStr = inputStr.replace('SSLv3_server_data.ssl_accept = & ssl3_accept;','SSLv3_server_data.ssl_accept = +0;')
  inputStr = inputStr.replace('void exit(int s)','void exitxxx(int s)')
  inputStr = inputStr.replace('100000','10')
  return inputStr

def afterTokenReplace(token):
  token = token.replace('sizeof\n(\nstruct\nwatchdog_info\n[\n1\n]\n)','sizeof\n(\nstruct\nwatchdog_info[\n\n1\n]\n)')
  token = token.replace('\n__attribute__',' __attribute__\n')
  return token
