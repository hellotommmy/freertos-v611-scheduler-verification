#ifndef EAL6_FREERTOS_V611_SCHEDULER_PORT_CONTRACT_H
#define EAL6_FREERTOS_V611_SCHEDULER_PORT_CONTRACT_H

/*
 * Observable sequential proof-port state.  These names deliberately make the
 * hardware boundary visible to CParser/AutoCorres instead of preprocessing a
 * reachable critical-section or yield operation to an empty token sequence.
 */
extern unsigned long eal6_port_critical_depth;
extern unsigned long eal6_port_interrupts_disabled;
extern unsigned long eal6_port_yield_count;

void eal6_port_enter_critical( void );
void eal6_port_exit_critical( void );
void eal6_port_disable_interrupts( void );
void eal6_port_enable_interrupts( void );
void eal6_port_yield( void );
unsigned long eal6_port_set_interrupt_mask_from_isr( void );
void eal6_port_clear_interrupt_mask_from_isr( unsigned long uxSavedMask );

#endif /* EAL6_FREERTOS_V611_SCHEDULER_PORT_CONTRACT_H */
