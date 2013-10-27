# 
# Copyright (c) 2013 Pantazis Deligiannis (p.deligiannis@imperial.ac.uk)
# This file is distributed under the MIT License. See LICENSE for details.
# 

cmake_minimum_required(VERSION 2.8)
project(smack)

if (NOT WIN32 OR MSYS OR CYGWIN)
  find_program(LLVM_CONFIG_EXECUTABLE NAMES llvm-config PATHS ${LLVM_CONFIG} NO_DEFAULT_PATH DOC "llvm-config")
	  
	if (LLVM_CONFIG_EXECUTABLE STREQUAL "LLVM_CONFIG_EXECUTABLE-NOTFOUND")
    message(FATAL_ERROR "llvm-config could not be found!")
  endif()
		
  execute_process(
    COMMAND ${LLVM_CONFIG_EXECUTABLE} --cxxflags
    OUTPUT_VARIABLE LLVM_CXXFLAGS
    OUTPUT_STRIP_TRAILING_WHITESPACE
  )
	
	set(LLVM_CXXFLAGS "${LLVM_CXXFLAGS} -fno-exceptions -fno-rtti")
	
  execute_process(
    COMMAND ${LLVM_CONFIG_EXECUTABLE} --libs
    OUTPUT_VARIABLE LLVM_LIBS
    OUTPUT_STRIP_TRAILING_WHITESPACE
  )
	
  execute_process(
    COMMAND ${LLVM_CONFIG_EXECUTABLE} --ldflags
    OUTPUT_VARIABLE LLVM_LDFLAGS
    OUTPUT_STRIP_TRAILING_WHITESPACE
  )
				
  if (${CMAKE_SYSTEM_NAME} MATCHES "Linux")
    set(LLVM_CXXFLAGS "${LLVM_CXXFLAGS} -std=c++0x -stdlib=libc++")
  endif()
  
  if (${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
    set(LLVM_CXXFLAGS "${LLVM_CXXFLAGS} -std=c++11 -stdlib=libc++")
  endif()
	
endif()

include_directories(include)

add_library(smackTranslator STATIC
	include/smack/smack.h
	include/smack/BoogieAst.h
	include/smack/BplPrinter.h
	include/smack/DSAAliasAnalysis.h
	include/smack/SmackInstGenerator.h
	include/smack/SmackModuleGenerator.h
	include/smack/SmackOptions.h
	include/smack/SmackRep.h
	include/smack/SmackRep2dMem.h
	include/smack/SmackRepFlatMem.h
  lib/smack/BoogieAst.cpp
	lib/smack/BplPrinter.cpp
	lib/smack/DSAAliasAnalysis.cpp
	lib/smack/SmackInstGenerator.cpp
	lib/smack/SmackModuleGenerator.cpp
	lib/smack/SmackOptions.cpp
	lib/smack/SmackRep.cpp
	lib/smack/SmackRep2dMem.cpp
	lib/smack/SmackRepFlatMem.cpp
)

add_executable(smack
  tools/smack/smack.cpp
)

set_target_properties(smack smackTranslator
    PROPERTIES COMPILE_FLAGS "${LLVM_CXXFLAGS}")

target_link_libraries(smackTranslator ${LLVM_LIBS} ${LLVM_LDFLAGS})
target_link_libraries(smack smackTranslator)
