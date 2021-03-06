add_subdirectory(avy)
add_subdirectory(seahorn)
add_subdirectory(Analysis)
add_subdirectory(Transforms)
add_subdirectory(Support)

add_llvm_loadable_module (shadow 
  Transforms/Instrumentation/ShadowMemDsa.cc 
  Transforms/Instrumentation/ShadowMemSeaDsa.cc 
  Transforms/Instrumentation/MixedSemantics.cc
  Transforms/Instrumentation/NondetInit.cc
  Transforms/Scalar/PromoteVerifierCalls.cc
  Transforms/Scalar/LowerGvInitializers.cc
  Transforms/Scalar/LoopUnhoist.cc
  Analysis/CanFail.cc
  Transforms/Utils/Local.cc
  )

target_link_libraries (shadow avy)
if (HAVE_DSA)
  target_link_libraries (shadow ${DSA_LIBS})
endif()
install (TARGETS shadow LIBRARY DESTINATION lib)

add_llvm_loadable_module (checks
  Transforms/Scalar/LowerCstExpr.cc
  Transforms/Instrumentation/BufferBoundsCheck.cc
  Transforms/Instrumentation/IntegerOverflowCheck.cc
  Analysis/CanAccessMemory.cc
)

target_link_libraries (checks avy)
install (TARGETS checks LIBRARY DESTINATION lib)
