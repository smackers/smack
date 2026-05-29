#
# This file is distributed under the MIT License. See LICENSE for details.
#

cmake_minimum_required(VERSION 3.20)
project(smack)
set(SMACK_CXX_STANDARD "23" CACHE STRING "C++ standard for SMACK targets (20 or 23). Default is 23; 20 stays in CI for one cycle.")
set_property(CACHE SMACK_CXX_STANDARD PROPERTY STRINGS "20" "23")
set(CMAKE_CXX_STANDARD ${SMACK_CXX_STANDARD})
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# LLVM discovery — uses llvm-config on every supported platform. The old
# Windows-specific hand-rolled lib-list branch was removed in Phase 1;
# modern LLVM ships a working CMake config + llvm-config on Windows too.
# WSL2 + the Ubuntu apt LLVM packages are the supported Windows path.
file(STRINGS "bin/versions" LLVM_VERSION_STR
  REGEX "LLVM_FULL_VERSION=\"[0-9]+\.[0-9]+\.[0-9]+")
string(REGEX MATCH "[0-9]+\.[0-9]+" LLVM_EXTENDED_VERSION "${LLVM_VERSION_STR}")

file(STRINGS "bin/versions" LLVM_VERSION_STR
  REGEX "LLVM_SHORT_VERSION=\"[0-9]+")
string(REGEX MATCH "[0-9]+" LLVM_SHORT_VERSION "${LLVM_VERSION_STR}")

find_program(LLVM_CONFIG_EXECUTABLE NAMES llvm-config-${LLVM_SHORT_VERSION}
  llvm-config PATHS ${LLVM_CONFIG} DOC "llvm-config")

if(LLVM_CONFIG_EXECUTABLE STREQUAL "LLVM_CONFIG_EXECUTABLE-NOTFOUND")
  message(FATAL_ERROR "llvm-config could not be found!")
endif()

execute_process(
  COMMAND ${LLVM_CONFIG_EXECUTABLE} --cxxflags
  OUTPUT_VARIABLE LLVM_CXXFLAGS
  OUTPUT_STRIP_TRAILING_WHITESPACE
)

# SMACK doesn't catch or throw exceptions, so -fno-exceptions is justified.
# SMACK doesn't use C++ runtime type identification features, so -fno-rtti
# is justified.
set(CMAKE_CXX_FLAGS
  "${LLVM_CXXFLAGS} -fno-exceptions -fno-rtti -O3")
set(SMACK_LLVM_COMPAT_HEADER
  "${CMAKE_CURRENT_SOURCE_DIR}/include/smack/LlvmCompat.h")

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

# Phase A3: per-target include directories. Previously these were two global
# `include_directories(include)` + `include_directories(sea-dsa/include)`
# calls that polluted every CMake target in the tree. Each SMACK target now
# gains the include search paths it actually needs via `target_include_directories`.
# sea-dsa/include is added via `target_include_directories(SeaDsaAnalysis ...)`
# after add_subdirectory below.
function(smack_force_llvm_compat target)
  target_compile_options(${target} PRIVATE
    "-include" "${SMACK_LLVM_COMPAT_HEADER}")
endfunction()

function(smack_target_setup target)
  # BUILD_INTERFACE for in-tree consumers; INSTALL_INTERFACE for downstream
  # projects pulling via find_package(smack CONFIG).
  target_include_directories(${target} PUBLIC
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
    $<INSTALL_INTERFACE:include>
  )
  smack_force_llvm_compat(${target})
endfunction()

add_library(utils STATIC
  include/utils/MergeGEP.h
  include/utils/SimplifyInsertValue.h
  include/utils/SimplifyExtractValue.h
  lib/utils/MergeGEP.cpp
  lib/utils/SimplifyInsertValue.cpp
  lib/utils/SimplifyExtractValue.cpp
)
smack_target_setup(utils)

add_library(smackTranslator STATIC
  include/smack/AddTiming.h
  include/smack/BoogieAst.h
  include/smack/BplFilePrinter.h
  include/smack/BplPrinter.h
  include/smack/DSAWrapper.h
  include/smack/DSAWrapperAnalysis.h
  include/smack/InitializePasses.h
  include/smack/LlvmCompat.h
  include/smack/Naming.h
  include/smack/Regions.h
  include/smack/SmackInstGenerator.h
  include/smack/SmackModuleGenerator.h
  include/smack/SmackOptions.h
  include/smack/CodifyStaticInits.h
  include/smack/RemoveDeadDefs.h
  include/smack/InitUndefAllocas.h
  include/smack/ExtractContracts.h
  include/smack/VerifierCodeMetadata.h
  include/smack/SimplifyLibCalls.h
  include/smack/SmackRep.h
  include/smack/DiffProductMatcher.h
  include/smack/SmackPipeline.h
  include/smack/VectorOperations.h
  include/smack/MemorySafetyChecker.h
  include/smack/IntegerOverflowChecker.h
  include/smack/RewriteBitwiseOps.h
  include/smack/NormalizeLoops.h
  include/smack/RustFixes.h
  include/smack/AnnotateLoopExits.h
  include/smack/SplitAggregateValue.h
  include/smack/Prelude.h
  include/smack/SmackWarnings.h
  lib/smack/AddTiming.cpp
  lib/smack/BoogieAst.cpp
  lib/smack/BplFilePrinter.cpp
  lib/smack/BplPrinter.cpp
  lib/smack/Debug.cpp
  lib/smack/DSAWrapper.cpp
  lib/smack/DSAWrapperAnalysis.cpp
  lib/smack/Naming.cpp
  lib/smack/Regions.cpp
  lib/smack/SmackInstGenerator.cpp
  lib/smack/SmackModuleGenerator.cpp
  lib/smack/SmackOptions.cpp
  lib/smack/CodifyStaticInits.cpp
  lib/smack/RemoveDeadDefs.cpp
  lib/smack/InitUndefAllocas.cpp
  lib/smack/ExtractContracts.cpp
  lib/smack/VerifierCodeMetadata.cpp
  lib/smack/SimplifyLibCalls.cpp
  lib/smack/SmackRep.cpp
  lib/smack/DiffProductMatcher.cpp
  lib/smack/SmackPipeline.cpp
  lib/smack/VectorOperations.cpp
  lib/smack/MemorySafetyChecker.cpp
  lib/smack/IntegerOverflowChecker.cpp
  lib/smack/RewriteBitwiseOps.cpp
  lib/smack/NormalizeLoops.cpp
  lib/smack/RustFixes.cpp
  lib/smack/AnnotateLoopExits.cpp
  lib/smack/SplitAggregateValue.cpp
  lib/smack/Prelude.cpp
  lib/smack/SmackWarnings.cpp
)
smack_target_setup(smackTranslator)

add_executable(llvm2bpl
  tools/llvm2bpl/llvm2bpl.cpp
)
smack_target_setup(llvm2bpl)

add_executable(llvm-diffmatch2bpl
  tools/diffmatch/llvm-diffmatch2bpl.cpp
)
smack_target_setup(llvm-diffmatch2bpl)

add_library(externalizePass STATIC
  tools/externalizer/ExternalizePass.h
  tools/externalizer/ExternalizePass.cpp
)
smack_target_setup(externalizePass)

add_executable(extern-statics
  tools/externalizer/extern-statics.cpp
)
smack_target_setup(extern-statics)

# Import LLVM's cmake definitions.
# Borrowed from https://github.com/banach-space/llvm-tutor/commit/72cb20d058b9b3f51717c7a17607f7a4c7398642
find_package (LLVM ${LLVM_EXTENDED_VERSION} REQUIRED CONFIG)
if (NOT ${LLVM_SHORT_VERSION} VERSION_EQUAL "${LLVM_VERSION_MAJOR}")
  message(FATAL_ERROR "Found LLVM ${LLVM_VERSION_MAJOR}, but need ${LLVM_SHORT_VERSION}")
endif ()
list(APPEND CMAKE_MODULE_PATH "${LLVM_CMAKE_DIR}")
include(AddLLVM)
include(HandleLLVMOptions)

# SVF (Andersen points-to) is the memory-region partitioner, replacing sea-dsa.
# It is a HARD, ungated dependency: DSAWrapper derives a sound disjoint region
# partition from SVF's inclusion-based points-to via union-find.
set(SVF_HOME "/home/ubuntu/SVF" CACHE PATH "SVF source+build root")
find_package(SVF REQUIRED CONFIG)
# SVF's exported targets advertise build-tree include dirs that may not exist in
# every layout (e.g. SVF::SvfFlags carries Release-build/include/SVF which is
# absent); filter to existing paths so target_include_directories doesn't error
# on a stale entry. SvfFlags must be included — SvfCore/SvfLLVM depend on it
# transitively, so its bad include would otherwise still propagate.
foreach(_svf_target SVF::SvfFlags SVF::SvfCore SVF::SvfLLVM)
  get_target_property(_svf_includes ${_svf_target} INTERFACE_INCLUDE_DIRECTORIES)
  if(_svf_includes)
    set(_svf_existing_includes "")
    foreach(_svf_include ${_svf_includes})
      if(EXISTS "${_svf_include}")
        list(APPEND _svf_existing_includes "${_svf_include}")
      endif()
    endforeach()
    set_target_properties(${_svf_target} PROPERTIES
      INTERFACE_INCLUDE_DIRECTORIES "${_svf_existing_includes}")
  endif()
endforeach()

target_link_libraries(smackTranslator ${LLVM_LIBS} ${LLVM_SYSTEM_LIBS}
  ${LLVM_LDFLAGS})
target_link_libraries(smackTranslator SVF::SvfLLVM SVF::SvfCore)

target_link_libraries(llvm2bpl smackTranslator utils)
target_link_libraries(llvm-diffmatch2bpl smackTranslator utils)

# SVF + its private LLVM-21 and z3 shared libs live outside the system loader
# path; bake their dirs into the RPATH of the tools that pull them in.
set(SMACK_SVF_RPATH
  "/home/ubuntu/SVF/Release-build/lib;/home/ubuntu/SVF/llvm-21.1.0.obj/lib;/home/ubuntu/SVF/z3.obj/bin")
set_target_properties(llvm2bpl llvm-diffmatch2bpl PROPERTIES
  BUILD_RPATH "${SMACK_SVF_RPATH}"
  INSTALL_RPATH "${SMACK_SVF_RPATH}")

target_link_libraries(externalizePass ${LLVM_LIBS} ${LLVM_SYSTEM_LIBS}
  ${LLVM_LDFLAGS})
target_link_libraries(extern-statics externalizePass)

install(TARGETS llvm2bpl llvm-diffmatch2bpl
  RUNTIME DESTINATION bin
)

install(TARGETS extern-statics
  RUNTIME DESTINATION bin
)

install(FILES
  ${CMAKE_CURRENT_SOURCE_DIR}/bin/smack
  ${CMAKE_CURRENT_SOURCE_DIR}/bin/smack-doctor
  ${CMAKE_CURRENT_SOURCE_DIR}/bin/smack-svcomp-wrapper.sh
  PERMISSIONS OWNER_EXECUTE OWNER_WRITE OWNER_READ
  GROUP_EXECUTE GROUP_READ WORLD_EXECUTE WORLD_READ
  DESTINATION bin
)

install(DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/share/smack
  DESTINATION share
  USE_SOURCE_PERMISSIONS
  FILES_MATCHING PATTERN "*.py" PATTERN "*.h" PATTERN "*.c" PATTERN "Makefile"
    PATTERN "*.rs" PATTERN "*.f90" PATTERN "*.di" PATTERN "*.toml"
    PATTERN "*.cpp" PATTERN "cassert" PATTERN "*.yaml"
)

option(SMACK_BUILD_TESTS "Build SMACK C++ unit tests (requires network for FetchContent)" OFF)
option(SMACK_NEW_PM "Use NewPM full pipeline in llvm2bpl (opt-in; Tier A+B+C+D via runSmackFullNewPM)" OFF)
if(SMACK_NEW_PM)
  target_compile_definitions(llvm2bpl PRIVATE SMACK_NEW_PM=1)
endif()
if(SMACK_BUILD_TESTS)
  enable_testing()
  add_subdirectory(unittests)
endif()

option(SMACK_BUILD_FUZZERS "Build libFuzzer harnesses under unittests/fuzz (requires clang)" OFF)
if(SMACK_BUILD_FUZZERS)
  add_subdirectory(unittests/fuzz)
endif()

install(FILES
  ${CMAKE_CURRENT_SOURCE_DIR}/bin/versions
  DESTINATION share/smack
  RENAME versions.py
)

install(FILES
  ${CMAKE_CURRENT_SOURCE_DIR}/share/smack/lib/smack/Cargo.toml
  ${CMAKE_CURRENT_SOURCE_DIR}/share/smack/lib/smack/build.rs
  DESTINATION share/smack/lib
)

install(FILES
  ${CMAKE_CURRENT_SOURCE_DIR}/share/smack/lib/smack-rust.c
  DESTINATION share/smack/lib/src
)

install(FILES
  ${CMAKE_CURRENT_SOURCE_DIR}/share/smack/lib/smack.rs
  DESTINATION share/smack/lib/src
  RENAME lib.rs
)

# Phase A6: export package config so downstream projects can do
#   find_package(smack REQUIRED CONFIG)
#   target_link_libraries(my_target PRIVATE smack::smackTranslator)
include(CMakePackageConfigHelpers)
include(GNUInstallDirs)

install(TARGETS smackTranslator utils
  EXPORT smackTargets
  ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}
  LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
  INCLUDES DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
)

install(EXPORT smackTargets
  FILE smack-targets.cmake
  NAMESPACE smack::
  DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/smack
)

configure_package_config_file(
  ${CMAKE_CURRENT_SOURCE_DIR}/cmake/smack-config.cmake.in
  ${CMAKE_CURRENT_BINARY_DIR}/smack-config.cmake
  INSTALL_DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/smack
  PATH_VARS CMAKE_INSTALL_INCLUDEDIR
)

# Read SMACK_VERSION from share/smack/constants.py — single source of
# truth that pyproject.toml also resolves dynamically via hatch.
file(STRINGS "share/smack/constants.py" SMACK_VERSION_STR
  REGEX "^VERSION[ \t]*=[ \t]*\"[0-9]+\\.[0-9]+\\.[0-9]+\"")
string(REGEX MATCH "[0-9]+\\.[0-9]+\\.[0-9]+" SMACK_VERSION "${SMACK_VERSION_STR}")
if(NOT SMACK_VERSION)
  message(FATAL_ERROR "Could not parse SMACK VERSION from share/smack/constants.py")
endif()

write_basic_package_version_file(
  ${CMAKE_CURRENT_BINARY_DIR}/smack-config-version.cmake
  VERSION ${SMACK_VERSION}
  COMPATIBILITY SameMajorVersion
)

install(FILES
  ${CMAKE_CURRENT_BINARY_DIR}/smack-config.cmake
  ${CMAKE_CURRENT_BINARY_DIR}/smack-config-version.cmake
  DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/smack
)

install(DIRECTORY include/ DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
  FILES_MATCHING PATTERN "*.h" PATTERN "*.hpp"
)
