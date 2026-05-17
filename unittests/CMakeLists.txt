include(FetchContent)

# Pin GoogleTest. Bump deliberately when LLVM/clang baseline shifts.
FetchContent_Declare(
  googletest
  GIT_REPOSITORY https://github.com/google/googletest.git
  GIT_TAG        v1.15.2
)

# SMACK builds with -fno-rtti / -fno-exceptions; gtest tolerates this.
set(gtest_force_shared_crt ON CACHE BOOL "" FORCE)
FetchContent_MakeAvailable(googletest)

include(GoogleTest)

add_executable(smack_unittests
  BoogieAstTest.cpp
  NamingTest.cpp
  NewPMSiblingsTest.cpp
  NewPMEdgeCasesTest.cpp
)

smack_force_llvm_compat(smack_unittests)

target_include_directories(smack_unittests PRIVATE
  ${CMAKE_SOURCE_DIR}/include
  ${CMAKE_SOURCE_DIR}/sea-dsa/include
)

target_link_libraries(smack_unittests PRIVATE
  -Wl,--start-group
  smackTranslator
  utils
  SeaDsaAnalysis
  -Wl,--end-group
  ${LLVM_LIBS}
  ${LLVM_SYSTEM_LIBS}
  ${LLVM_LDFLAGS}
  GTest::gtest
  GTest::gtest_main
)

gtest_discover_tests(smack_unittests)
