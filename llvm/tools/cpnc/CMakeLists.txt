if("X86" IN_LIST LLVM_TARGETS_TO_BUILD)
  set(LLVM_LINK_COMPONENTS Core Support Target MC CodeGen X86)
  set(LLVM_REQUIRES_EH ON)
  set(LLVM_REQUIRES_RTTI ON)
  add_custom_command(OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/UnicodeData.inc
    COMMAND "${Python3_EXECUTABLE}" "${CMAKE_CURRENT_SOURCE_DIR}/utils/native_ucd.py"
            "${CMAKE_CURRENT_SOURCE_DIR}/unicode/ucd17.json.gz"
            "${CMAKE_CURRENT_BINARY_DIR}/UnicodeData.inc"
    DEPENDS utils/native_ucd.py unicode/ucd17.json.gz VERBATIM)
  add_llvm_tool(cpnc
    Binding.cpp
    Closure.cpp
    Construction.cpp
    Dispatch.cpp
    Driver.cpp
    Emit.cpp
    Floating.cpp
    Generic.cpp
    Integer.cpp
    Lexer.cpp
    Lifetime.cpp
    Parser.cpp
    Reservations.cpp
    Sema.cpp
    SpecialMembers.cpp
    Storage.cpp
    Tagged.cpp
    ${CMAKE_CURRENT_BINARY_DIR}/UnicodeData.inc
  )
  target_include_directories(cpnc PRIVATE ${CMAKE_CURRENT_BINARY_DIR})
  if(LLVM_INCLUDE_TESTS AND CMAKE_SYSTEM_NAME STREQUAL "Linux" AND
     CMAKE_HOST_SYSTEM_PROCESSOR MATCHES "^(x86_64|AMD64)$" AND NOT CMAKE_CROSSCOMPILING)
    add_custom_target(check-cpnc
      COMMAND "${CMAKE_COMMAND}" -E env "CPNC=$<TARGET_FILE:cpnc>"
        "PATH=${LLVM_RUNTIME_OUTPUT_INTDIR}:$ENV{PATH}" "${Python3_EXECUTABLE}"
        "${CMAKE_CURRENT_SOURCE_DIR}/tests/test_cpnc.py" -v
      DEPENDS cpnc llvm-as USES_TERMINAL)
  endif()
endif()
