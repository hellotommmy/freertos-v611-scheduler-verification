#ifndef EAL6_FREERTOS_V611_SCHEDULER_PROOF_CONFIG_H
#define EAL6_FREERTOS_V611_SCHEDULER_PROOF_CONFIG_H

/*
 * Frozen proof configuration for the scheduler translation unit.
 * These values make every branch used by scope/semantic_slice.json explicit.
 * They do not select a deployed board or claim hardware equivalence.
 */
#define configCPU_CLOCK_HZ                      1000000UL
#define configTICK_RATE_HZ                      1000UL
#define configMAX_PRIORITIES                    4
#define configMINIMAL_STACK_SIZE                128
#define configTOTAL_HEAP_SIZE                   8192UL
#define configMAX_TASK_NAME_LEN                 16

#define configUSE_PREEMPTION                    1
#define configUSE_IDLE_HOOK                     0
#define configUSE_TICK_HOOK                     0
#define configUSE_CO_ROUTINES                   0
#define configUSE_16_BIT_TICKS                  0
#define configUSE_TRACE_FACILITY                0
#define configGENERATE_RUN_TIME_STATS           0
#define configCHECK_FOR_STACK_OVERFLOW          0
#define configUSE_MUTEXES                       0
#define configUSE_RECURSIVE_MUTEXES             0
#define configUSE_COUNTING_SEMAPHORES           0
#define configUSE_APPLICATION_TASK_TAG          0
#define configUSE_MALLOC_FAILED_HOOK            0
#define configUSE_ALTERNATIVE_API               0
#define configQUEUE_REGISTRY_SIZE               0
#define configIDLE_SHOULD_YIELD                 1

/* Keep the seven switches from the list-smoke proof configuration fixed. */
#define INCLUDE_vTaskPrioritySet                1
#define INCLUDE_uxTaskPriorityGet               1
#define INCLUDE_vTaskDelete                     1
#define INCLUDE_vTaskCleanUpResources           1
#define INCLUDE_vTaskSuspend                    1
#define INCLUDE_vTaskDelayUntil                 1
#define INCLUDE_vTaskDelay                      1

/* Defaults in FreeRTOS.h are repeated here so the active TU is reproducible. */
#define INCLUDE_xTaskResumeFromISR              1
#define INCLUDE_uxTaskGetStackHighWaterMark     0
#define INCLUDE_xTaskGetCurrentTaskHandle       0
#define INCLUDE_xTaskGetSchedulerState          0

#endif /* EAL6_FREERTOS_V611_SCHEDULER_PROOF_CONFIG_H */
