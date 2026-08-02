/*
 * Link closure for the frozen P2 layout artifact.
 *
 * The proof translation unit is compiled unchanged.  These definitions close
 * hardware, allocator, and C-library references that are outside the P2
 * vTaskDelay execution slice.  The artifact is never executed; the functions
 * exist only so GNU ld can produce a fully linked, inspectable ELF32 image.
 */

#include "FreeRTOS.h"
#include "task.h"
#include "scheduler_port_contract.h"
#include <stddef.h>
#include <string.h>

/* Fail compilation if GCC's target ABI drifts from StrictCParser's ABI. */
typedef char eal6_pointer_is_32_bits[(sizeof(void *) == 4U) ? 1 : -1];
typedef char eal6_ulong_is_32_bits[(sizeof(unsigned long) == 4U) ? 1 : -1];
typedef char eal6_port_base_is_32_bits[(sizeof(portBASE_TYPE) == 4U) ? 1 : -1];
typedef char eal6_tick_is_32_bits[(sizeof(portTickType) == 4U) ? 1 : -1];
typedef char eal6_list_is_20_bytes[(sizeof(xList) == 20U) ? 1 : -1];
typedef char eal6_item_is_20_bytes[(sizeof(xListItem) == 20U) ? 1 : -1];
typedef char eal6_mini_item_is_12_bytes[(sizeof(xMiniListItem) == 12U) ? 1 : -1];

static volatile unsigned long eal6_frozen_entry_sink;

portSTACK_TYPE *pxPortInitialiseStack(
    portSTACK_TYPE *pxTopOfStack,
    pdTASK_CODE pxCode,
    void *pvParameters )
{
    ( void ) pxTopOfStack;
    ( void ) pxCode;
    ( void ) pvParameters;
    return ( portSTACK_TYPE * ) 0;
}

void *pvPortMalloc( size_t xSize )
{
    ( void ) xSize;
    return ( void * ) 0;
}

void vPortFree( void *pv )
{
    ( void ) pv;
}

void vPortInitialiseBlocks( void )
{
}

size_t xPortGetFreeHeapSize( void )
{
    return ( size_t ) 0;
}

portBASE_TYPE xPortStartScheduler( void )
{
    return ( portBASE_TYPE ) pdFAIL;
}

void vPortEndScheduler( void )
{
}

char *strncpy( char *pxDestination, const char *pxSource, size_t xCount )
{
    size_t xIndex;
    for( xIndex = 0; xIndex < xCount; ++xIndex )
    {
        char c = pxSource[ xIndex ];
        pxDestination[ xIndex ] = c;
        if( c == '\0' )
        {
            ++xIndex;
            while( xIndex < xCount )
            {
                pxDestination[ xIndex ] = '\0';
                ++xIndex;
            }
            break;
        }
    }
    return pxDestination;
}

void *memset( void *pxDestination, int iValue, size_t xCount )
{
    unsigned char *pucDestination = ( unsigned char * ) pxDestination;
    size_t xIndex;
    for( xIndex = 0; xIndex < xCount; ++xIndex )
    {
        pucDestination[ xIndex ] = ( unsigned char ) iValue;
    }
    return pxDestination;
}

/* Fixed entry symbol for ET_EXEC.  This artifact is not a runnable kernel. */
void eal6_frozen_entry( void )
{
    for( ;; )
    {
        ++eal6_frozen_entry_sink;
    }
}
