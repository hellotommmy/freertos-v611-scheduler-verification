theory List_V611_Raw_Skip_Translation
  imports "AutoCorres2_Main.AutoCorres_Main"
begin

text \<open>
  Official AutoCorres alternative-path audit: disable the split-heap phase for
  the whole unmodified list.c translation.  This is an abstraction-level
  choice only; the stock source and proof-port headers are byte-identical to
  the primary translation.
\<close>

setup \<open>fn thy =>
  let
    val cpp = Resources.master_directory thy +
      Path.explode "../../scripts/cpp-wsl.sh"
    val _ = File.check_file cpp
  in Config.put_global IsarInstall.cpp_path (File.standard_path cpp) thy end\<close>

include_C_file "../../proof_port/FreeRTOSConfig.h" for "list.c"
include_C_file "../../proof_port/portmacro.h" for "list.c"
include_C_file "../../proof_port/stddef.h" for "list.c"
include_C_file "../../proof_port/stdlib.h" for "list.c"
include_C_file "../../upstream/FreeRTOSV6.1.1/Source/include/FreeRTOS.h" for "list.c"
include_C_file "../../upstream/FreeRTOSV6.1.1/Source/include/list.h" for "list.c"
include_C_file "../../upstream/FreeRTOSV6.1.1/Source/include/mpu_wrappers.h" for "list.c"
include_C_file "../../upstream/FreeRTOSV6.1.1/Source/include/portable.h" for "list.c"
include_C_file "../../upstream/FreeRTOSV6.1.1/Source/include/projdefs.h" for "list.c"

new_C_include_dir "../../proof_port"
new_C_include_dir "../../upstream/FreeRTOSV6.1.1/Source/include"

install_C_file "../../upstream/FreeRTOSV6.1.1/Source/list.c"

autocorres [
  skip_heap_abs,
  no_body =
    pxPortInitialiseStack
    pvPortMalloc
    vPortFree
    vPortInitialiseBlocks
    xPortGetFreeHeapSize
    xPortStartScheduler
    vPortEndScheduler,
  ts_rules = nondet
] "list.c"

print_statement vListInitialise'_def
print_statement vListInitialiseItem'_def
print_statement vListInsertEnd'_def
print_statement vListRemove'_def

end
