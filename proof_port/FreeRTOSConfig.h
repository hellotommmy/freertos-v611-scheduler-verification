#ifndef EAL6_FREERTOS_V611_PROOF_CONFIG_H
#define EAL6_FREERTOS_V611_PROOF_CONFIG_H

/*
 * Proof-environment configuration for the source-only list.c translation.
 * Every setting is audited in PROOF_PORT_LEDGER.md.  This header is supplied
 * on the include path; no upstream FreeRTOS source file is modified.
 */

#define configUSE_PREEMPTION                    1
#define configUSE_IDLE_HOOK                     0
#define configUSE_TICK_HOOK                     0
#define configUSE_CO_ROUTINES                   0
#define configUSE_16_BIT_TICKS                  0

#define INCLUDE_vTaskPrioritySet                1
#define INCLUDE_uxTaskPriorityGet               1
#define INCLUDE_vTaskDelete                     1
#define INCLUDE_vTaskCleanUpResources           1
#define INCLUDE_vTaskSuspend                    1
#define INCLUDE_vTaskDelayUntil                 1
#define INCLUDE_vTaskDelay                      1

#endif /* EAL6_FREERTOS_V611_PROOF_CONFIG_H */
