# Bundle the Python front end as a single relocatable driver beside llc.
if(Python3_VERSION VERSION_GREATER_EQUAL 3.10 AND UNIX)
  set(cpnc_sources
    frontend/__main__.py
    frontend/identifiers.py
    frontend/inheritance.py
    frontend/ucd17.json.gz
    frontend/UNICODE-LICENSE.txt
    frontend/compiler.py
    frontend/constant.py
    frontend/constraints.py
    frontend/construction.py
    frontend/control.py
    frontend/dispatch.py
    frontend/memory.py
    frontend/lifecycle.py
    frontend/numeric.py
    frontend/packs.py
    frontend/syntax.py
    frontend/statics.py
    frontend/tagged.py)
  set(cpnc_stage "${CMAKE_CURRENT_BINARY_DIR}/python")
  set(cpnc_driver "${LLVM_RUNTIME_OUTPUT_INTDIR}/cpnc")
  add_custom_command(
    OUTPUT "${cpnc_driver}"
    COMMAND "${CMAKE_COMMAND}" -E make_directory "${cpnc_stage}" "${LLVM_RUNTIME_OUTPUT_INTDIR}"
    COMMAND "${CMAKE_COMMAND}" -E copy_if_different ${cpnc_sources} "${cpnc_stage}"
    COMMAND "${Python3_EXECUTABLE}" -m zipapp
            "${cpnc_stage}" -p "/usr/bin/env python3"
            -o "${cpnc_driver}"
    WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}"
    DEPENDS ${cpnc_sources}
    VERBATIM)
  add_custom_target(cpnc DEPENDS "${cpnc_driver}")
  if("X86" IN_LIST LLVM_TARGETS_TO_BUILD)
    add_dependencies(cpnc llc)
    if(LLVM_INCLUDE_TESTS AND CMAKE_SYSTEM_NAME STREQUAL "Linux" AND
       CMAKE_HOST_SYSTEM_PROCESSOR MATCHES "^(x86_64|AMD64)$" AND NOT CMAKE_CROSSCOMPILING)
      add_custom_target(check-cpnc
        COMMAND "${CMAKE_COMMAND}" -E env "CPNC=${cpnc_driver}"
                "PATH=${LLVM_RUNTIME_OUTPUT_INTDIR}:$ENV{PATH}"
                "${Python3_EXECUTABLE}" "${CMAKE_CURRENT_SOURCE_DIR}/tests/test_cpnc.py" -v
        DEPENDS cpnc llvm-as
        USES_TERMINAL)
    endif()
  endif()
endif()
