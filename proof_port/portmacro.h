#ifndef EAL6_FREERTOS_V611_PROOF_PORTMACRO_H
#define EAL6_FREERTOS_V611_PROOF_PORTMACRO_H

/* Scalar choices follow the 32-bit C machine used by the CParser smoke. */
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

#define portSTACK_GROWTH        ( -1 )
#define portTICK_RATE_MS        ( ( portTickType ) 1 )
#define portBYTE_ALIGNMENT      4

/*
 * list.c does not invoke these macros.  They are declarations of an external
 * proof-port boundary only, not a model of interrupt or scheduler behaviour.
 */
#define portENTER_CRITICAL()
#define portEXIT_CRITICAL()
#define portDISABLE_INTERRUPTS()
#define portENABLE_INTERRUPTS()
#define portYIELD()

#endif /* EAL6_FREERTOS_V611_PROOF_PORTMACRO_H */
