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

add_library(assistDS STATIC
	include/assistDS/ArgCast.h
	include/assistDS/FuncSimplify.h
	include/assistDS/Int2PtrCmp.h
	include/assistDS/SimplifyExtractValue.h
	include/assistDS/StructReturnToPointer.h
	include/assistDS/DSNodeEquivs.h
	include/assistDS/FuncSpec.h
	include/assistDS/SimplifyGEP.h
	include/assistDS/TypeChecks.h
	include/assistDS/DataStructureCallGraph.h
	include/assistDS/GEPExprArgs.h
	include/assistDS/LoadArgs.h
	include/assistDS/SimplifyInsertValue.h
	include/assistDS/TypeChecksOpt.h
	include/assistDS/Devirt.h
	include/assistDS/IndCloner.h
	include/assistDS/MergeGEP.h
	include/assistDS/SimplifyLoad.h
	lib/AssistDS/ArgCast.cpp
	lib/AssistDS/Devirt.cpp
	lib/AssistDS/GEPExprArgs.cpp
	lib/AssistDS/LoadArgs.cpp
	lib/AssistDS/SimplifyExtractValue.cpp
	lib/AssistDS/StructReturnToPointer.cpp
	lib/AssistDS/ArgSimplify.cpp
	lib/AssistDS/DynCount.cpp
	lib/AssistDS/IndCloner.cpp
	lib/AssistDS/SimplifyGEP.cpp
	lib/AssistDS/TypeChecks.cpp
	lib/AssistDS/DSNodeEquivs.cpp
	lib/AssistDS/FuncSimplify.cpp
	lib/AssistDS/Int2PtrCmp.cpp
	lib/AssistDS/MergeGEP.cpp
	lib/AssistDS/SimplifyInsertValue.cpp
	lib/AssistDS/TypeChecksOpt.cpp
	lib/AssistDS/DataStructureCallGraph.cpp
	lib/AssistDS/FuncSpec.cpp
	lib/AssistDS/SVADevirt.cpp
	lib/AssistDS/SimplifyLoad.cpp
)

add_library(dsa STATIC
	include/dsa/AddressTakenAnalysis.h
	include/dsa/DSCallGraph.h
	include/dsa/DSNode.h
	include/dsa/EntryPointAnalysis.h
	include/dsa/keyiterator.h
	include/dsa/svset.h
	include/dsa/AllocatorIdentification.h
	include/dsa/DSGraph.h
	include/dsa/DSSupport.h
	include/dsa/stl_util.h
	include/dsa/CallTargets.h
	include/dsa/DSGraphTraits.h
	include/dsa/DataStructure.h
	include/dsa/TypeSafety.h
	include/dsa/super_set.h
	lib/dsa/AddressTakenAnalysis.cpp
	lib/dsa/CallTargets.cpp
	lib/dsa/DSTest.cpp
	lib/dsa/EquivClassGraphs.cpp
	lib/dsa/StdLibPass.cpp
	lib/dsa/AllocatorIdentification.cpp
	lib/dsa/CompleteBottomUp.cpp
	lib/dsa/DataStructure.cpp
	lib/dsa/GraphChecker.cpp
	lib/dsa/Printer.cpp
	lib/dsa/TopDownClosure.cpp
	lib/dsa/Basic.cpp
	lib/dsa/DSCallGraph.cpp
	lib/dsa/DataStructureStats.cpp
	lib/dsa/TypeSafety.cpp
	lib/dsa/BottomUpClosure.cpp
	lib/dsa/DSGraph.cpp
	lib/dsa/EntryPointAnalysis.cpp
	lib/dsa/Local.cpp
	lib/dsa/SanityCheck.cpp
)

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

set_target_properties(smack smackTranslator assistDS dsa
    PROPERTIES COMPILE_FLAGS "${LLVM_CXXFLAGS}")

target_link_libraries(smackTranslator ${LLVM_LIBS} ${LLVM_LDFLAGS})
target_link_libraries(smack smackTranslator assistDS dsa)
