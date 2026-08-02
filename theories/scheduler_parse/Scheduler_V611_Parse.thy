theory Scheduler_V611_Parse
  imports "AutoCorres2_P2_Layout_Main.AutoCorres_Main"
begin

text \<open>
  CParser gate for a proof-only composition unit containing the unmodified
  FreeRTOS V6.1.1 tasks.c and list.c bodies plus the named sequential port
  contract.  No scheduler refinement theorem is claimed by this parse gate.
\<close>

setup \<open>fn thy =>
  let
    val cpp = Resources.master_directory thy +
      Path.explode "../../scripts/cpp-wsl.sh"
    val _ = File.check_file cpp
  in Config.put_global IsarInstall.cpp_path (File.standard_path cpp) thy end\<close>

text \<open>
  The build wrapper regenerates this ML manifest only after rebuilding and
  checking the frozen ELF with independent readelf/nm paths, exact input and
  evidence hashes, DWARF sizes, symbol completeness, and the pinned ELF hash.
  The patched CParser declares ordinary definitions for exactly the six data
  globals in that manifest while retaining its stock path when no manifest is
  configured.
\<close>

ML_file "../../build/generated/P2_Root_Address_Config.ML"

setup \<open>
  Config.put_global CalculateState.addressed_global_definitions
    P2_Root_Address_Config.configuration
\<close>

include_C_file "../../proof_port/scheduler/FreeRTOSConfig.h"
  for "scheduler_translation_unit.c"
include_C_file "../../proof_port/scheduler/portmacro.h"
  for "scheduler_translation_unit.c"
include_C_file "../../proof_port/scheduler/scheduler_port_contract.h"
  for "scheduler_translation_unit.c"
include_C_file "../../proof_port/scheduler/scheduler_port_contract.c"
  for "scheduler_translation_unit.c"
include_C_file "../../proof_port/scheduler/stdio.h"
  for "scheduler_translation_unit.c"
include_C_file "../../proof_port/scheduler/string.h"
  for "scheduler_translation_unit.c"
include_C_file "../../proof_port/stddef.h"
  for "scheduler_translation_unit.c"
include_C_file "../../proof_port/stdlib.h"
  for "scheduler_translation_unit.c"
include_C_file "../../upstream/FreeRTOSV6.1.1/Source/include/FreeRTOS.h"
  for "scheduler_translation_unit.c"
include_C_file "../../upstream/FreeRTOSV6.1.1/Source/include/list.h"
  for "scheduler_translation_unit.c"
include_C_file "../../upstream/FreeRTOSV6.1.1/Source/include/mpu_wrappers.h"
  for "scheduler_translation_unit.c"
include_C_file "../../upstream/FreeRTOSV6.1.1/Source/include/portable.h"
  for "scheduler_translation_unit.c"
include_C_file "../../upstream/FreeRTOSV6.1.1/Source/include/projdefs.h"
  for "scheduler_translation_unit.c"
include_C_file "../../upstream/FreeRTOSV6.1.1/Source/include/StackMacros.h"
  for "scheduler_translation_unit.c"
include_C_file "../../upstream/FreeRTOSV6.1.1/Source/include/task.h"
  for "scheduler_translation_unit.c"
include_C_file "../../upstream/FreeRTOSV6.1.1/Source/tasks.c"
  for "scheduler_translation_unit.c"
include_C_file "../../upstream/FreeRTOSV6.1.1/Source/list.c"
  for "scheduler_translation_unit.c"

new_C_include_dir "../../proof_port/scheduler"
new_C_include_dir "../../proof_port"
new_C_include_dir "../../upstream/FreeRTOSV6.1.1/Source/include"
new_C_include_dir "../../upstream/FreeRTOSV6.1.1/Source"

install_C_file "../../proof_port/scheduler/scheduler_translation_unit.c"

end
