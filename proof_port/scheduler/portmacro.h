#ifndef EAL6_FREERTOS_V611_SCHEDULER_PORTMACRO_H
#define EAL6_FREERTOS_V611_SCHEDULER_PORTMACRO_H

#include "scheduler_port_contract.h"

/* Scalar choices match the 32-bit CParser machine used by the list smoke. */
#define portCHAR        char
#define portFLOAT       float
#define portDOUBLE      double
#define portLONG        long
#define portSHORT       short
#define portSTACK_TYPE  unsigned long
#define portBASE_TYPE   long

#if ( configUSE_16_BIT_TICKS == 1 )
typedef unsigned short portTickType;
#define portMAX_DELAY ( ( portTickType ) 0xffffU )
#else
typedef unsigned long portTickType;
#define portMAX_DELAY ( ( portTickType ) 0xffffffffUL )
#endif

#define portSTACK_GROWTH              ( -1 )
#define portTICK_RATE_MS              ( ( portTickType ) 1 )
#define portBYTE_ALIGNMENT            4
#define portCRITICAL_NESTING_IN_TCB   0
#define portNUM_CONFIGURABLE_REGIONS  1
#define portPRIVILEGE_BIT             ( ( unsigned portBASE_TYPE ) 0x00 )
#define portTASK_FUNCTION_PROTO( vFunction, pvParameters ) \
    void vFunction( void *pvParameters )
#define portTASK_FUNCTION( vFunction, pvParameters ) \
    void vFunction( void *pvParameters )

/* Reachable scheduler boundaries have named, executable proof contracts. */
#define portENTER_CRITICAL()          eal6_port_enter_critical()
#define portEXIT_CRITICAL()           eal6_port_exit_critical()
#define portDISABLE_INTERRUPTS()      eal6_port_disable_interrupts()
#define portENABLE_INTERRUPTS()       eal6_port_enable_interrupts()
#define portYIELD()                   eal6_port_yield()
#define portSET_INTERRUPT_MASK_FROM_ISR() \
    eal6_port_set_interrupt_mask_from_isr()
#define portCLEAR_INTERRUPT_MASK_FROM_ISR( uxSavedStatusValue ) \
    eal6_port_clear_interrupt_mask_from_isr( uxSavedStatusValue )

#endif /* EAL6_FREERTOS_V611_SCHEDULER_PORTMACRO_H */
