#
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
    COMMAND ${LLVM_CONFIG_EXECUTABLE} --system-libs
    OUTPUT_VARIABLE LLVM_SYSTEM_LIBS
    OUTPUT_STRIP_TRAILING_WHITESPACE
  )

  execute_process(
    COMMAND ${LLVM_CONFIG_EXECUTABLE} --ldflags
    OUTPUT_VARIABLE LLVM_LDFLAGS
    OUTPUT_STRIP_TRAILING_WHITESPACE
  )

else()
  set(LLVM_SRC "" CACHE PATH "LLVM source directory")
  set(LLVM_BUILD "" CACHE PATH "LLVM build directory")
  set(LLVM_BUILD_TYPE "" CACHE STRING "LLVM build type")

  if (NOT EXISTS "${LLVM_SRC}/include/llvm")
    message(FATAL_ERROR "Invalid LLVM source directory: ${LLVM_SRC}")
  endif()

  set(LLVM_LIBDIR "${LLVM_BUILD}/lib/${LLVM_BUILD_TYPE}")
  if (NOT EXISTS "${LLVM_LIBDIR}")
    message(FATAL_ERROR "Invalid LLVM build directory: ${LLVM_BUILD}")
  endif()

  set(LLVM_CXXFLAGS "\"/I${LLVM_SRC}/include\" \"/I${LLVM_BUILD}/include\" -D_SCL_SECURE_NO_WARNINGS -wd4146 -wd4244 -wd4355 -wd4482 -wd4800")
  set(LLVM_LDFLAGS "")
  set(LLVM_LIBS "${LLVM_LIBDIR}/LLVMTransformUtils.lib" "${LLVM_LIBDIR}/LLVMipa.lib" "${LLVM_LIBDIR}/LLVMAnalysis.lib" "${LLVM_LIBDIR}/LLVMTarget.lib" "${LLVM_LIBDIR}/LLVMMC.lib" "${LLVM_LIBDIR}/LLVMObject.lib" "${LLVM_LIBDIR}/LLVMBitReader.lib" "${LLVM_LIBDIR}/LLVMCore.lib" "${LLVM_LIBDIR}/LLVMSupport.lib")

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
  lib/DSA/AddressTakenAnalysis.cpp
  lib/DSA/CallTargets.cpp
  lib/DSA/DSTest.cpp
  lib/DSA/EquivClassGraphs.cpp
  lib/DSA/StdLibPass.cpp
  lib/DSA/AllocatorIdentification.cpp
  lib/DSA/CompleteBottomUp.cpp
  lib/DSA/DataStructure.cpp
  lib/DSA/GraphChecker.cpp
  lib/DSA/Printer.cpp
  lib/DSA/TopDownClosure.cpp
  lib/DSA/Basic.cpp
  lib/DSA/DSCallGraph.cpp
  lib/DSA/DataStructureStats.cpp
  lib/DSA/TypeSafety.cpp
  lib/DSA/BottomUpClosure.cpp
  lib/DSA/DSGraph.cpp
  lib/DSA/EntryPointAnalysis.cpp
  lib/DSA/Local.cpp
  lib/DSA/SanityCheck.cpp
)

add_library(smackTranslator STATIC
  include/smack/BoogieAst.h
  include/smack/BplFilePrinter.h
  include/smack/BplPrinter.h
  include/smack/Contracts.h
  include/smack/DSAAliasAnalysis.h
  include/smack/Naming.h
  include/smack/Slicing.h
  include/smack/SmackInstGenerator.h
  include/smack/SmackModuleGenerator.h
  include/smack/SmackOptions.h
  include/smack/SmackRep.h
  include/smack/SmackRepFlatMem.h
  lib/smack/BoogieAst.cpp
  lib/smack/BplFilePrinter.cpp
  lib/smack/BplPrinter.cpp
  lib/smack/Contracts.cpp
  lib/smack/DSAAliasAnalysis.cpp
  lib/smack/Naming.cpp
  lib/smack/Slicing.cpp
  lib/smack/SmackInstGenerator.cpp
  lib/smack/SmackModuleGenerator.cpp
  lib/smack/SmackOptions.cpp
  lib/smack/SmackRep.cpp
  lib/smack/SmackRepFlatMem.cpp
)

add_executable(smack
  tools/smack/smack.cpp
)

set_target_properties(smack smackTranslator assistDS dsa
    PROPERTIES COMPILE_FLAGS "${LLVM_CXXFLAGS}")

target_link_libraries(smackTranslator ${LLVM_LIBS} ${LLVM_SYSTEM_LIBS} ${LLVM_LDFLAGS})
target_link_libraries(smack smackTranslator assistDS dsa)

INSTALL(TARGETS smack
  RUNTIME DESTINATION bin
)

INSTALL(FILES ${CMAKE_CURRENT_SOURCE_DIR}/bin/boogie
  ${CMAKE_CURRENT_SOURCE_DIR}/bin/corral
  ${CMAKE_CURRENT_SOURCE_DIR}/bin/llvm2bpl.py
  ${CMAKE_CURRENT_SOURCE_DIR}/bin/smackgen.py
  ${CMAKE_CURRENT_SOURCE_DIR}/bin/smackverify.py
  PERMISSIONS OWNER_EXECUTE OWNER_WRITE OWNER_READ
  GROUP_EXECUTE GROUP_READ WORLD_EXECUTE WORLD_READ
  DESTINATION bin
)

INSTALL(FILES ${CMAKE_CURRENT_SOURCE_DIR}/include/smack/smack.h
  ${CMAKE_CURRENT_SOURCE_DIR}/include/smack/smack-contracts.h
  ${CMAKE_CURRENT_SOURCE_DIR}/include/smack/smack-svcomp.h
  PERMISSIONS OWNER_EXECUTE OWNER_WRITE OWNER_READ
  GROUP_EXECUTE GROUP_READ WORLD_EXECUTE WORLD_READ
  DESTINATION include/smack
)

