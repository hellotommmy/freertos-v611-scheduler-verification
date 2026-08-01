#include "scheduler_port_contract.h"

unsigned long eal6_port_critical_depth = 0UL;
unsigned long eal6_port_interrupts_disabled = 0UL;
unsigned long eal6_port_yield_count = 0UL;

void eal6_port_enter_critical( void )
{
    ++eal6_port_critical_depth;
    eal6_port_interrupts_disabled = 1UL;
}

void eal6_port_exit_critical( void )
{
    if( eal6_port_critical_depth > 0UL )
    {
        --eal6_port_critical_depth;
    }

    if( eal6_port_critical_depth == 0UL )
    {
        eal6_port_interrupts_disabled = 0UL;
    }
}

void eal6_port_disable_interrupts( void )
{
    eal6_port_interrupts_disabled = 1UL;
}

void eal6_port_enable_interrupts( void )
{
    eal6_port_interrupts_disabled = 0UL;
}

void eal6_port_yield( void )
{
    ++eal6_port_yield_count;
}

unsigned long eal6_port_set_interrupt_mask_from_isr( void )
{
    unsigned long uxPreviousMask = eal6_port_interrupts_disabled;
    eal6_port_interrupts_disabled = 1UL;
    return uxPreviousMask;
}

void eal6_port_clear_interrupt_mask_from_isr( unsigned long uxSavedMask )
{
    eal6_port_interrupts_disabled = uxSavedMask;
}
