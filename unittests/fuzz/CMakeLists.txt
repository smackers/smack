# libFuzzer targets. Off by default; enable with -DSMACK_BUILD_FUZZERS=ON.
# Requires clang (libFuzzer is a clang sanitizer runtime). Each fuzzer
# uses -fsanitize=fuzzer,address,undefined so it doubles as ASan/UBSan
# regression bait.

if(NOT CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
  message(FATAL_ERROR
    "SMACK_BUILD_FUZZERS=ON requires clang (libFuzzer is clang-only). "
    "Re-configure with -DCMAKE_CXX_COMPILER=clang++ -DCMAKE_C_COMPILER=clang.")
endif()

set(SMACK_FUZZ_FLAGS
  "-fsanitize=fuzzer,address,undefined"
  "-fno-omit-frame-pointer"
  "-fno-sanitize-recover=undefined"
  "-g")

# smack_add_fuzzer(name source [link_targets...])
#   Without link_targets the fuzzer only needs LLVM. Pass
#   smackTranslator (and friends) to harnesses that reach SMACK code.
function(smack_add_fuzzer name source)
  add_executable(${name} ${source})
  smack_force_llvm_compat(${name})
  target_include_directories(${name} PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${CMAKE_SOURCE_DIR}/sea-dsa/include
  )
  target_compile_options(${name} PRIVATE ${SMACK_FUZZ_FLAGS})
  target_link_options(${name} PRIVATE ${SMACK_FUZZ_FLAGS})
  target_link_libraries(${name} PRIVATE
    ${ARGN}
    ${LLVM_LIBS}
    ${LLVM_SYSTEM_LIBS}
    ${LLVM_LDFLAGS}
  )
endfunction()

# Pure-LLVM harness: just exercises parseBitcodeFile + module walks.
smack_add_fuzzer(fuzz_bitcode_parse fuzz_bitcode_parse.cpp)

# SMACK BoogieAst printer round-trip — needs smackTranslator for the
# Expr/Stmt/Decl factories + printers.
smack_add_fuzzer(fuzz_boogie_ast_print fuzz_boogie_ast_print.cpp
  smackTranslator
  utils)

# Convenience aggregate target so CI can `cmake --build build --target fuzzers`.
add_custom_target(fuzzers DEPENDS
  fuzz_bitcode_parse
  fuzz_boogie_ast_print)
