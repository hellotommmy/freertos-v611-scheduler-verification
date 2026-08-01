/*
 * Source-level scheduler trace for the untouched FreeRTOS V6.1.1 tasks.c and
 * list.c files.  This is a runnable observation harness, not a replacement
 * scheduler.  Scenario setup constructs valid source states; every transition
 * under test is performed by an upstream function or macro.
 *
 * WSL is LP64, while the proof port and StrictCParser machine use 32-bit long.
 * The small port block below mirrors the proof-port values with fixed-width
 * host types so tick wrap is real uint32_t wrap, not a harness assignment.
 * The named proof-port critical/yield bodies are included unchanged.
 */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../proof_port/scheduler/scheduler_port_contract.h"

#define portCHAR        char
#define portFLOAT       float
#define portDOUBLE      double
#define portLONG        int
#define portSHORT       short
#define portSTACK_TYPE  uint32_t
#define portBASE_TYPE   int

typedef uint32_t portTickType;

#define portMAX_DELAY                  ( ( portTickType ) UINT32_MAX )
#define portSTACK_GROWTH               ( -1 )
#define portTICK_RATE_MS               ( ( portTickType ) 1U )
#define portBYTE_ALIGNMENT             4
#define portCRITICAL_NESTING_IN_TCB    0
#define portNUM_CONFIGURABLE_REGIONS   1
#define portPRIVILEGE_BIT              ( ( unsigned portBASE_TYPE ) 0U )
#define portTASK_FUNCTION_PROTO( vFunction, pvParameters ) \
    void vFunction( void *pvParameters )
#define portTASK_FUNCTION( vFunction, pvParameters ) \
    void vFunction( void *pvParameters )

#define portENTER_CRITICAL()           eal6_port_enter_critical()
#define portEXIT_CRITICAL()            eal6_port_exit_critical()
#define portDISABLE_INTERRUPTS()       eal6_port_disable_interrupts()
#define portENABLE_INTERRUPTS()        eal6_port_enable_interrupts()
#define portYIELD()                    eal6_port_yield()
#define portSET_INTERRUPT_MASK_FROM_ISR() \
    eal6_port_set_interrupt_mask_from_isr()
#define portCLEAR_INTERRUPT_MASK_FROM_ISR( uxSavedStatusValue ) \
    eal6_port_clear_interrupt_mask_from_isr( uxSavedStatusValue )

/* Direct textual composition: all three bodies below are unmodified files. */
#include "../proof_port/scheduler/scheduler_port_contract.c"
#include "../upstream/FreeRTOSV6.1.1/Source/tasks.c"
#include "../upstream/FreeRTOSV6.1.1/Source/list.c"

#define TRACE_MAX_TASKS 8U
#define TRACE_LIST_COUNT ( configMAX_PRIORITIES + 4U )

typedef struct TraceTask
{
    const char *name;
    tskTCB tcb;
} TraceTask;

typedef struct TraceListRef
{
    const char *name;
    const xList *list;
    int ready_priority;
    int ordered;
} TraceListRef;

static TraceTask *trace_tasks[ TRACE_MAX_TASKS ];
static unsigned trace_task_count;
static const char *trace_scenario = "startup";
static const char *trace_step = "startup";

typedef enum TracePhase
{
    TraceStableRunning,
    TraceYieldPending
} TracePhase;

static TracePhase trace_phase = TraceStableRunning;

static const char *trace_phase_name( void )
{
    return trace_phase == TraceStableRunning
        ? "StableRunning"
        : "YieldPending";
}

static void trace_fatal( const char *kind, const char *id, unsigned line )
{
    printf( "{\"kind\":\"%s\",\"scenario\":\"%s\","
            "\"step\":\"%s\",\"id\":\"%s\",\"line\":%u}\n",
            kind, trace_scenario, trace_step, id, line );
    fflush( stdout );
    exit( 90 );
}

#define TRACE_REQUIRE( condition, id ) \
    do \
    { \
        if( !( condition ) ) \
        { \
            trace_fatal( "invariant_failure", ( id ), __LINE__ ); \
        } \
    } while( 0 )

static void trace_check( const char *id, int condition )
{
    printf( "{\"kind\":\"check\",\"scenario\":\"%s\","
            "\"step\":\"%s\",\"id\":\"%s\",\"ok\":%s}\n",
            trace_scenario, trace_step, id, condition ? "true" : "false" );
    fflush( stdout );
    if( !condition )
    {
        exit( 91 );
    }
}

/*
 * These are link-closure stubs for task-creation/start/heap paths that none of
 * the four scenarios may reach.  A reached stub emits JSON and terminates; it
 * never returns a fabricated stack, allocation, or scheduler result.
 */
static void trace_stub_reached( const char *name )
{
    trace_fatal( "stub_reached", name, __LINE__ );
}

portSTACK_TYPE *pxPortInitialiseStack(
    portSTACK_TYPE *pxTopOfStack,
    pdTASK_CODE pxCode,
    void *pvParameters )
{
    ( void ) pxTopOfStack;
    ( void ) pxCode;
    ( void ) pvParameters;
    trace_stub_reached( "pxPortInitialiseStack" );
    return NULL;
}

void *pvPortMalloc( size_t xSize )
{
    ( void ) xSize;
    trace_stub_reached( "pvPortMalloc" );
    return NULL;
}

void vPortFree( void *pv )
{
    ( void ) pv;
    trace_stub_reached( "vPortFree" );
}

void vPortInitialiseBlocks( void )
{
    trace_stub_reached( "vPortInitialiseBlocks" );
}

size_t xPortGetFreeHeapSize( void )
{
    trace_stub_reached( "xPortGetFreeHeapSize" );
    return 0U;
}

portBASE_TYPE xPortStartScheduler( void )
{
    trace_stub_reached( "xPortStartScheduler" );
    return ( portBASE_TYPE ) pdFAIL;
}

void vPortEndScheduler( void )
{
    trace_stub_reached( "vPortEndScheduler" );
}

static void set_trace_step( const char *step )
{
    trace_step = step;
}

static TraceListRef trace_list_ref( unsigned index )
{
    static const char * const ready_names[ configMAX_PRIORITIES ] =
    {
        "ready[0]", "ready[1]", "ready[2]", "ready[3]"
    };
    TraceListRef ref;

    if( index < configMAX_PRIORITIES )
    {
        ref.name = ready_names[ index ];
        ref.list = ( const xList * ) &( pxReadyTasksLists[ index ] );
        ref.ready_priority = ( int ) index;
        ref.ordered = 0;
    }
    else if( index == configMAX_PRIORITIES )
    {
        ref.name = "delayed1";
        ref.list = &xDelayedTaskList1;
        ref.ready_priority = -1;
        ref.ordered = 1;
    }
    else if( index == configMAX_PRIORITIES + 1U )
    {
        ref.name = "delayed2";
        ref.list = &xDelayedTaskList2;
        ref.ready_priority = -1;
        ref.ordered = 1;
    }
    else if( index == configMAX_PRIORITIES + 2U )
    {
        ref.name = "pending_ready";
        ref.list = &xPendingReadyList;
        ref.ready_priority = -1;
        ref.ordered = 0;
    }
    else
    {
        ref.name = "suspended";
        ref.list = &xSuspendedTaskList;
        ref.ready_priority = -1;
        ref.ordered = 0;
    }
    return ref;
}

static const char *list_name( const xList *list )
{
    unsigned index;
    if( list == NULL )
    {
        return "NULL";
    }
    for( index = 0U; index < TRACE_LIST_COUNT; ++index )
    {
        TraceListRef ref = trace_list_ref( index );
        if( ref.list == list )
        {
            return ref.name;
        }
    }
    return "UNKNOWN_LIST";
}

static TraceTask *task_from_tcb( const tskTCB *tcb )
{
    unsigned index;
    for( index = 0U; index < trace_task_count; ++index )
    {
        if( &( trace_tasks[ index ]->tcb ) == tcb )
        {
            return trace_tasks[ index ];
        }
    }
    return NULL;
}

static TraceTask *task_from_item(
    const volatile xListItem *item,
    const char **item_kind )
{
    unsigned index;
    for( index = 0U; index < trace_task_count; ++index )
    {
        if( item == &( trace_tasks[ index ]->tcb.xGenericListItem ) )
        {
            *item_kind = "generic";
            return trace_tasks[ index ];
        }
        if( item == &( trace_tasks[ index ]->tcb.xEventListItem ) )
        {
            *item_kind = "event";
            return trace_tasks[ index ];
        }
    }
    *item_kind = "unknown";
    return NULL;
}

static const char *task_name( const tskTCB *tcb )
{
    TraceTask *task;
    if( tcb == NULL )
    {
        return "NULL";
    }
    task = task_from_tcb( tcb );
    return task == NULL ? "UNKNOWN_TASK" : task->name;
}

static const char *item_name(
    const xList *list,
    const volatile xListItem *item )
{
    const volatile xListItem *sentinel =
        ( const volatile xListItem * ) &( list->xListEnd );
    const char *kind;
    TraceTask *task;
    if( item == sentinel )
    {
        return "END";
    }
    task = task_from_item( item, &kind );
    ( void ) kind;
    return task == NULL ? "UNKNOWN_ITEM" : task->name;
}

static void reset_scheduler( const char *scenario )
{
    trace_scenario = scenario;
    trace_step = "reset";
    trace_phase = TraceStableRunning;
    trace_task_count = 0U;

    /* This is the untouched source initialiser, visible through textual include. */
    prvInitialiseTaskLists();

    pxCurrentTCB = NULL;
    xTickCount = ( portTickType ) 0U;
    uxTopUsedPriority = tskIDLE_PRIORITY;
    uxTopReadyPriority = tskIDLE_PRIORITY;
    xSchedulerRunning = pdTRUE;
    uxSchedulerSuspended = ( unsigned portBASE_TYPE ) pdFALSE;
    uxMissedTicks = 0U;
    xMissedYield = pdFALSE;
    xNumOfOverflows = 0;
    uxCurrentNumberOfTasks = 0U;
    uxTaskNumber = 0U;
    uxTasksDeleted = 0U;

    eal6_port_critical_depth = 0UL;
    eal6_port_interrupts_disabled = 0UL;
    eal6_port_yield_count = 0UL;
}

static void init_trace_task(
    TraceTask *task,
    const char *name,
    unsigned portBASE_TYPE priority )
{
    unsigned index;
    size_t name_length = strlen( name );

    TRACE_REQUIRE( trace_task_count < TRACE_MAX_TASKS, "registry.capacity" );
    TRACE_REQUIRE( priority < configMAX_PRIORITIES, "task.priority.in_range" );
    TRACE_REQUIRE( name_length > 0U, "task.name.nonempty" );

    memset( task, 0, sizeof( *task ) );
    task->name = name;
    task->tcb.uxPriority = priority;
    vListInitialiseItem( &( task->tcb.xGenericListItem ) );
    vListInitialiseItem( &( task->tcb.xEventListItem ) );
    listSET_LIST_ITEM_OWNER( &( task->tcb.xGenericListItem ), &( task->tcb ) );
    listSET_LIST_ITEM_OWNER( &( task->tcb.xEventListItem ), &( task->tcb ) );
    listSET_LIST_ITEM_VALUE(
        &( task->tcb.xEventListItem ),
        ( portTickType ) ( configMAX_PRIORITIES - priority ) );

    for( index = 0U; index + 1U < configMAX_TASK_NAME_LEN; ++index )
    {
        task->tcb.pcTaskName[ index ] =
            ( signed char ) ( index < name_length ? name[ index ] : '\0' );
    }
    task->tcb.pcTaskName[ configMAX_TASK_NAME_LEN - 1U ] = '\0';

    trace_tasks[ trace_task_count ] = task;
    ++trace_task_count;
    ++uxCurrentNumberOfTasks;
    ++uxTaskNumber;
    if( priority > uxTopUsedPriority )
    {
        uxTopUsedPriority = priority;
    }
}

static void add_ready( TraceTask *task )
{
    tskTCB *tcb = &( task->tcb );
    TRACE_REQUIRE(
        task->tcb.xGenericListItem.pvContainer == NULL,
        "setup.ready_requires_detached" );
    listSET_LIST_ITEM_VALUE( &( task->tcb.xGenericListItem ), 0U );
    /* The V6.1.1 macro parameter is unparenthesised; pass a simple lvalue. */
    prvAddTaskToReadyQueue( tcb );
}

static void add_delayed(
    TraceTask *task,
    xList *list,
    portTickType wake_tick )
{
    TRACE_REQUIRE(
        task->tcb.xGenericListItem.pvContainer == NULL,
        "setup.delay_requires_detached" );
    TRACE_REQUIRE(
        list == pxDelayedTaskList || list == pxOverflowDelayedTaskList,
        "setup.delay_role_known" );
    listSET_LIST_ITEM_VALUE( &( task->tcb.xGenericListItem ), wake_tick );
    vListInsert( list, &( task->tcb.xGenericListItem ) );
}

static unsigned item_occurrences(
    const xList *list,
    const volatile xListItem *wanted )
{
    const volatile xListItem *sentinel =
        ( const volatile xListItem * ) &( list->xListEnd );
    const volatile xListItem *node = list->xListEnd.pxNext;
    unsigned result = 0U;
    unsigned visited = 0U;

    while( node != sentinel )
    {
        TRACE_REQUIRE( visited < TRACE_MAX_TASKS * 2U, "topology.finite" );
        if( node == wanted )
        {
            ++result;
        }
        node = node->pxNext;
        ++visited;
    }
    return result;
}

static void validate_list( const TraceListRef *ref )
{
    const xList *list = ref->list;
    const volatile xListItem *sentinel =
        ( const volatile xListItem * ) &( list->xListEnd );
    const volatile xListItem *node = list->xListEnd.pxNext;
    const volatile xListItem *previous = sentinel;
    portTickType previous_key = 0U;
    unsigned have_previous_key = 0U;
    unsigned visited = 0U;
    int cursor_seen = ( list->pxIndex == sentinel );

    TRACE_REQUIRE(
        list->xListEnd.xItemValue == portMAX_DELAY,
        "topology.sentinel_max_key" );
    TRACE_REQUIRE(
        list->xListEnd.pxNext->pxPrevious == sentinel,
        "topology.sentinel_next_reverse" );
    TRACE_REQUIRE(
        list->xListEnd.pxPrevious->pxNext == sentinel,
        "topology.sentinel_previous_forward" );

    while( node != sentinel )
    {
        const char *kind;
        TraceTask *task;
        TRACE_REQUIRE( visited < TRACE_MAX_TASKS * 2U, "topology.no_short_cycle" );
        task = task_from_item( node, &kind );
        TRACE_REQUIRE( task != NULL, "topology.known_item" );
        TRACE_REQUIRE( node->pxPrevious == previous, "topology.previous_exact" );
        TRACE_REQUIRE( node->pxNext->pxPrevious == node, "topology.next_reverse" );
        TRACE_REQUIRE( node->pxPrevious->pxNext == node, "topology.previous_forward" );
        TRACE_REQUIRE(
            node->pvContainer == ( const void * ) list,
            "topology.container_exact" );
        TRACE_REQUIRE(
            node->pvOwner == ( const void * ) &( task->tcb ),
            "topology.owner_exact" );
        if( ref->ready_priority >= 0 )
        {
            TRACE_REQUIRE(
                strcmp( kind, "generic" ) == 0,
                "ready.generic_item_only" );
            TRACE_REQUIRE(
                task->tcb.uxPriority ==
                    ( unsigned portBASE_TYPE ) ref->ready_priority,
                "ready.priority_matches_list" );
        }
        if( ref->ordered && have_previous_key )
        {
            TRACE_REQUIRE(
                previous_key <= node->xItemValue,
                "delayed.nondecreasing_wake_keys" );
        }
        previous_key = node->xItemValue;
        have_previous_key = 1U;
        previous = node;
        if( list->pxIndex == node )
        {
            cursor_seen = 1;
        }
        node = node->pxNext;
        ++visited;
    }

    TRACE_REQUIRE( previous == list->xListEnd.pxPrevious, "topology.last_exact" );
    TRACE_REQUIRE(
        visited == ( unsigned ) list->uxNumberOfItems,
        "topology.count_exact" );
    TRACE_REQUIRE( cursor_seen, "topology.cursor_member_or_end" );
}

static void validate_scheduler_state( void )
{
    unsigned list_index;
    unsigned task_index;
    unsigned highest_ready = 0U;
    int found_ready = 0;

    TRACE_REQUIRE(
        pxDelayedTaskList != pxOverflowDelayedTaskList,
        "roles.delayed_overflow_distinct" );
    TRACE_REQUIRE(
        ( pxDelayedTaskList == &xDelayedTaskList1 &&
          pxOverflowDelayedTaskList == &xDelayedTaskList2 ) ||
        ( pxDelayedTaskList == &xDelayedTaskList2 &&
          pxOverflowDelayedTaskList == &xDelayedTaskList1 ),
        "roles.partition_physical_lists" );
    TRACE_REQUIRE(
        uxTopReadyPriority < configMAX_PRIORITIES,
        "globals.top_ready_in_range" );
    TRACE_REQUIRE(
        uxSchedulerSuspended == 0U,
        "globals.scheduler_not_suspended" );
    TRACE_REQUIRE(
        eal6_port_critical_depth == 0UL &&
        eal6_port_interrupts_disabled == 0UL,
        "port.boundary_quiescent" );

    for( list_index = 0U; list_index < TRACE_LIST_COUNT; ++list_index )
    {
        TraceListRef ref = trace_list_ref( list_index );
        validate_list( &ref );
    }

    for( list_index = configMAX_PRIORITIES; list_index > 0U; --list_index )
    {
        unsigned priority = list_index - 1U;
        if( pxReadyTasksLists[ priority ].uxNumberOfItems != 0U )
        {
            highest_ready = priority;
            found_ready = 1;
            break;
        }
    }
    TRACE_REQUIRE( found_ready, "ready.at_least_current_task" );
    if( trace_phase == TraceStableRunning )
    {
        TRACE_REQUIRE(
            uxTopReadyPriority == highest_ready,
            "globals.top_ready_exact_at_stable_boundary" );
    }
    else
    {
        TRACE_REQUIRE(
            uxTopReadyPriority >= highest_ready,
            "globals.top_ready_upper_bound_while_yield_pending" );
    }

    TRACE_REQUIRE( pxCurrentTCB != NULL, "current.nonnull" );
    TRACE_REQUIRE(
        task_from_tcb( ( const tskTCB * ) pxCurrentTCB ) != NULL,
        "current.known_tcb" );
    TRACE_REQUIRE(
        pxCurrentTCB->uxPriority < configMAX_PRIORITIES,
        "current.priority_in_range" );
    if( trace_phase == TraceStableRunning )
    {
        TRACE_REQUIRE(
            pxCurrentTCB->xGenericListItem.pvContainer ==
                ( const void * )
                    &( pxReadyTasksLists[ pxCurrentTCB->uxPriority ] ),
            "current.is_ready_at_stable_boundary" );
    }
    else
    {
        TRACE_REQUIRE(
            pxCurrentTCB->xGenericListItem.pvContainer ==
                ( const void * ) pxDelayedTaskList ||
            pxCurrentTCB->xGenericListItem.pvContainer ==
                ( const void * ) pxOverflowDelayedTaskList,
            "current.is_blocked_while_yield_pending" );
        TRACE_REQUIRE(
            eal6_port_yield_count > 0UL,
            "yield_pending.has_observable_request" );
    }

    for( task_index = 0U; task_index < trace_task_count; ++task_index )
    {
        TraceTask *task = trace_tasks[ task_index ];
        const volatile xListItem *items[ 2 ];
        unsigned item_index;
        items[ 0 ] = &( task->tcb.xGenericListItem );
        items[ 1 ] = &( task->tcb.xEventListItem );

        for( item_index = 0U; item_index < 2U; ++item_index )
        {
            unsigned occurrences = 0U;
            const void *container = items[ item_index ]->pvContainer;
            for( list_index = 0U; list_index < TRACE_LIST_COUNT; ++list_index )
            {
                TraceListRef ref = trace_list_ref( list_index );
                occurrences += item_occurrences( ref.list, items[ item_index ] );
            }
            TRACE_REQUIRE(
                occurrences <= 1U,
                "membership.item_occurs_at_most_once" );
            TRACE_REQUIRE(
                ( container == NULL && occurrences == 0U ) ||
                ( container != NULL && occurrences == 1U ),
                "membership.container_iff_occurs" );
            if( container != NULL )
            {
                TRACE_REQUIRE(
                    strcmp( list_name( ( const xList * ) container ),
                            "UNKNOWN_LIST" ) != 0,
                    "membership.container_known" );
            }
        }
    }
}

static void print_list_json( const TraceListRef *ref )
{
    const xList *list = ref->list;
    const volatile xListItem *sentinel =
        ( const volatile xListItem * ) &( list->xListEnd );
    const volatile xListItem *node = list->xListEnd.pxNext;
    unsigned visited = 0U;

    printf( "{\"name\":\"%s\",\"count\":%u,\"cursor\":\"%s\",\"ring\":[",
            ref->name,
            ( unsigned ) list->uxNumberOfItems,
            item_name( list, list->pxIndex ) );
    while( node != sentinel )
    {
        const char *kind;
        TraceTask *task = task_from_item( node, &kind );
        if( visited != 0U )
        {
            putchar( ',' );
        }
        printf( "{\"task\":\"%s\",\"item\":\"%s\",\"key\":%lu,"
                "\"previous\":\"%s\",\"next\":\"%s\"}",
                task->name,
                kind,
                ( unsigned long ) node->xItemValue,
                item_name( list, node->pxPrevious ),
                item_name( list, node->pxNext ) );
        node = node->pxNext;
        ++visited;
    }
    printf( "]}" );
}

static void trace_snapshot( const char *step )
{
    unsigned index;
    set_trace_step( step );
    validate_scheduler_state();

    printf( "{\"kind\":\"snapshot\",\"scenario\":\"%s\"," 
            "\"step\":\"%s\",\"phase\":\"%s\",\"tick\":%lu,"
            "\"current\":\"%s\"," 
            "\"top_ready\":%u,\"scheduler_running\":%ld,"
            "\"scheduler_suspended\":%u,\"missed_ticks\":%u,"
            "\"missed_yield\":%ld,\"overflows\":%ld,"
            "\"delayed_role\":\"%s\",\"overflow_role\":\"%s\","
            "\"port\":{\"critical_depth\":%lu,\"interrupts_disabled\":%lu,"
            "\"yield_count\":%lu},\"lists\":[",
            trace_scenario,
            trace_step,
            trace_phase_name(),
            ( unsigned long ) xTickCount,
            task_name( ( const tskTCB * ) pxCurrentTCB ),
            ( unsigned ) uxTopReadyPriority,
            ( long ) xSchedulerRunning,
            ( unsigned ) uxSchedulerSuspended,
            ( unsigned ) uxMissedTicks,
            ( long ) xMissedYield,
            ( long ) xNumOfOverflows,
            list_name( ( const xList * ) pxDelayedTaskList ),
            list_name( ( const xList * ) pxOverflowDelayedTaskList ),
            eal6_port_critical_depth,
            eal6_port_interrupts_disabled,
            eal6_port_yield_count );

    for( index = 0U; index < TRACE_LIST_COUNT; ++index )
    {
        TraceListRef ref = trace_list_ref( index );
        if( index != 0U )
        {
            putchar( ',' );
        }
        print_list_json( &ref );
    }

    printf( "],\"tasks\":[" );
    for( index = 0U; index < trace_task_count; ++index )
    {
        TraceTask *task = trace_tasks[ index ];
        if( index != 0U )
        {
            putchar( ',' );
        }
        printf( "{\"id\":\"%s\",\"priority\":%u,"
                "\"current\":%s,\"generic_key\":%lu,"
                "\"generic_container\":\"%s\","
                "\"event_container\":\"%s\"}",
                task->name,
                ( unsigned ) task->tcb.uxPriority,
                pxCurrentTCB == &( task->tcb ) ? "true" : "false",
                ( unsigned long ) task->tcb.xGenericListItem.xItemValue,
                list_name( ( const xList * )
                    task->tcb.xGenericListItem.pvContainer ),
                list_name( ( const xList * )
                    task->tcb.xEventListItem.pvContainer ) );
    }
    printf( "],\"invariants\":\"ok\"}\n" );
    fflush( stdout );
}

static void scenario_tick_no_wake( void )
{
    TraceTask running;
    TraceTask sleeping;

    reset_scheduler( "tick_no_wake" );
    init_trace_task( &running, "RUN", 2U );
    init_trace_task( &sleeping, "SLEEP", 1U );
    add_ready( &running );
    add_delayed( &sleeping, ( xList * ) pxDelayedTaskList, 7U );
    pxCurrentTCB = &( running.tcb );
    xTickCount = 5U;
    trace_snapshot( "before_tick" );

    vTaskIncrementTick();
    set_trace_step( "after_tick" );
    trace_check( "tick.incremented_once", xTickCount == 6U );
    trace_check(
        "tick.future_delay_not_woken",
        sleeping.tcb.xGenericListItem.pvContainer == pxDelayedTaskList );
    trace_check(
        "tick.current_unchanged_without_switch",
        pxCurrentTCB == &( running.tcb ) );
    trace_snapshot( "after_tick" );
}

static void scenario_tick_wakes_task( void )
{
    TraceTask low;
    TraceTask high;

    reset_scheduler( "tick_wakes_delayed" );
    init_trace_task( &low, "LOW", 1U );
    init_trace_task( &high, "HIGH", 3U );
    add_ready( &low );
    add_delayed( &high, ( xList * ) pxDelayedTaskList, 10U );
    pxCurrentTCB = &( low.tcb );
    xTickCount = 9U;
    trace_snapshot( "before_tick" );

    vTaskIncrementTick();
    set_trace_step( "after_tick" );
    trace_check( "tick.reaches_wake_key", xTickCount == 10U );
    trace_check(
        "tick.removes_expired_delayed_item",
        pxDelayedTaskList->uxNumberOfItems == 0U );
    trace_check(
        "tick.woken_task_enters_priority_ready_fifo",
        high.tcb.xGenericListItem.pvContainer ==
            ( const void * ) &( pxReadyTasksLists[ 3 ] ) );
    trace_check( "tick.raises_top_ready_priority", uxTopReadyPriority == 3U );
    trace_check(
        "tick.does_not_directly_switch_current",
        pxCurrentTCB == &( low.tcb ) );
    trace_snapshot( "after_tick" );

    vTaskSwitchContext();
    set_trace_step( "after_switch" );
    trace_check(
        "switch.selects_new_highest_priority",
        pxCurrentTCB == &( high.tcb ) );
    trace_snapshot( "after_switch" );
}

static void scenario_tick_wrap( void )
{
    TraceTask running;
    TraceTask wrapped;
    xList *old_delayed;
    xList *old_overflow;

    reset_scheduler( "tick_wrap_swaps_delay_roles" );
    init_trace_task( &running, "RUN", 1U );
    init_trace_task( &wrapped, "WRAP", 2U );
    add_ready( &running );
    add_delayed( &wrapped, ( xList * ) pxOverflowDelayedTaskList, 1U );
    pxCurrentTCB = &( running.tcb );
    xTickCount = portMAX_DELAY;
    old_delayed = ( xList * ) pxDelayedTaskList;
    old_overflow = ( xList * ) pxOverflowDelayedTaskList;
    set_trace_step( "before_wrap" );
    trace_check(
        "wrap.requires_old_current_delayed_empty",
        old_delayed->uxNumberOfItems == 0U );
    trace_snapshot( "before_wrap" );

    vTaskIncrementTick();
    set_trace_step( "after_wrap" );
    trace_check( "wrap.tick_is_zero", xTickCount == 0U );
    trace_check( "wrap.overflow_counter_increments", xNumOfOverflows == 1 );
    trace_check(
        "wrap.old_overflow_becomes_current_delayed",
        pxDelayedTaskList == old_overflow );
    trace_check(
        "wrap.old_delayed_becomes_overflow",
        pxOverflowDelayedTaskList == old_delayed );
    trace_check(
        "wrap.future_key_remains_delayed_at_zero",
        wrapped.tcb.xGenericListItem.pvContainer == pxDelayedTaskList );
    trace_snapshot( "after_wrap" );

    vTaskIncrementTick();
    set_trace_step( "after_tick_one" );
    trace_check( "post_wrap.tick_reaches_one", xTickCount == 1U );
    trace_check(
        "post_wrap.task_wakes_from_swapped_list",
        wrapped.tcb.xGenericListItem.pvContainer ==
            ( const void * ) &( pxReadyTasksLists[ 2 ] ) );
    trace_snapshot( "after_tick_one" );
}

static void scenario_same_priority_fifo( void )
{
    TraceTask a;
    TraceTask b;
    TraceTask c;

    reset_scheduler( "same_priority_switch_fifo" );
    init_trace_task( &a, "A", 2U );
    init_trace_task( &b, "B", 2U );
    init_trace_task( &c, "C", 2U );
    add_ready( &a );
    add_ready( &b );
    add_ready( &c );
    pxCurrentTCB = &( a.tcb );
    xTickCount = 42U;
    trace_snapshot( "before_switch" );

    vTaskSwitchContext();
    set_trace_step( "switch_1" );
    trace_check(
        "fifo.bootstrap_selects_first_inserted",
        pxCurrentTCB == &( a.tcb ) );
    trace_snapshot( "switch_1" );

    vTaskSwitchContext();
    set_trace_step( "switch_2" );
    trace_check( "fifo.second_is_B", pxCurrentTCB == &( b.tcb ) );
    trace_snapshot( "switch_2" );

    vTaskSwitchContext();
    set_trace_step( "switch_3" );
    trace_check( "fifo.third_is_C", pxCurrentTCB == &( c.tcb ) );
    trace_snapshot( "switch_3" );

    vTaskSwitchContext();
    set_trace_step( "switch_4" );
    trace_check( "fifo.wraps_back_to_A", pxCurrentTCB == &( a.tcb ) );
    trace_check(
        "fifo.switch_preserves_ring_order",
        pxReadyTasksLists[ 2 ].xListEnd.pxNext == &( a.tcb.xGenericListItem ) &&
        a.tcb.xGenericListItem.pxNext == &( b.tcb.xGenericListItem ) &&
        b.tcb.xGenericListItem.pxNext == &( c.tcb.xGenericListItem ) );
    trace_snapshot( "switch_4" );
}

static void scenario_delay_positive_no_wrap( void )
{
    TraceTask idle;
    TraceTask running;

    reset_scheduler( "delay_positive_no_wrap" );
    init_trace_task( &idle, "IDLE", 0U );
    init_trace_task( &running, "RUN", 2U );
    add_ready( &idle );
    add_ready( &running );
    pxCurrentTCB = &( running.tcb );
    xTickCount = 5U;
    trace_snapshot( "before_delay" );

    vTaskDelay( 2U );
    trace_phase = TraceYieldPending;
    set_trace_step( "after_delay" );
    trace_check( "delay.tick_framed", xTickCount == 5U );
    trace_check(
        "delay.current_identity_waits_for_port_switch",
        pxCurrentTCB == &( running.tcb ) );
    trace_check(
        "delay.current_removed_from_ready",
        running.tcb.xGenericListItem.pvContainer !=
            ( const void * ) &( pxReadyTasksLists[ 2 ] ) );
    trace_check(
        "delay.nonwrap_enters_current_delayed",
        running.tcb.xGenericListItem.pvContainer ==
            ( const void * ) pxDelayedTaskList );
    trace_check(
        "delay.nonwrap_wake_key_is_seven",
        running.tcb.xGenericListItem.xItemValue == 7U );
    trace_check(
        "delay.lower_priority_task_remains_ready",
        idle.tcb.xGenericListItem.pvContainer ==
            ( const void * ) &( pxReadyTasksLists[ 0 ] ) );
    trace_check(
        "delay.requests_exactly_one_yield",
        eal6_port_yield_count == 1UL );
    trace_check(
        "delay.top_ready_cache_can_be_stale",
        uxTopReadyPriority == 2U &&
        pxReadyTasksLists[ 2 ].uxNumberOfItems == 0U );
    trace_snapshot( "after_delay" );
}

static void scenario_delay_positive_wrap( void )
{
    TraceTask idle;
    TraceTask running;
    xList *old_delayed;
    xList *old_overflow;

    reset_scheduler( "delay_positive_wrap" );
    init_trace_task( &idle, "IDLE", 0U );
    init_trace_task( &running, "RUN", 2U );
    add_ready( &idle );
    add_ready( &running );
    pxCurrentTCB = &( running.tcb );
    xTickCount = portMAX_DELAY - 1U;
    old_delayed = ( xList * ) pxDelayedTaskList;
    old_overflow = ( xList * ) pxOverflowDelayedTaskList;
    trace_snapshot( "before_delay" );

    vTaskDelay( 3U );
    trace_phase = TraceYieldPending;
    set_trace_step( "after_delay" );
    trace_check(
        "delay_wrap.tick_framed",
        xTickCount == portMAX_DELAY - 1U );
    trace_check(
        "delay_wrap.wake_key_wraps_to_one",
        running.tcb.xGenericListItem.xItemValue == 1U );
    trace_check(
        "delay_wrap.enters_overflow_delayed",
        running.tcb.xGenericListItem.pvContainer ==
            ( const void * ) old_overflow );
    trace_check(
        "delay_wrap.does_not_swap_physical_roles",
        pxDelayedTaskList == old_delayed &&
        pxOverflowDelayedTaskList == old_overflow );
    trace_check(
        "delay_wrap.current_identity_waits_for_port_switch",
        pxCurrentTCB == &( running.tcb ) );
    trace_check(
        "delay_wrap.requests_exactly_one_yield",
        eal6_port_yield_count == 1UL );
    trace_snapshot( "after_delay" );
}

int main( void )
{
    printf( "{\"kind\":\"meta\",\"source\":\"FreeRTOS V6.1.1 untouched tasks.c+list.c\","
            "\"composition\":\"direct_textual_include\","
            "\"proof_port_contract\":\"included_unchanged\","
            "\"port_type_adapter\":\"fixed-width mirror of 32-bit proof ABI\","
            "\"host_unsigned_long_bits\":%u,\"tick_bits\":%u,"
            "\"port_base_bits\":%u,"
            "\"stub_policy\":\"record JSON and terminate; never fabricate state\","
            "\"stubs\":[\"pxPortInitialiseStack\",\"pvPortMalloc\","
            "\"vPortFree\",\"vPortInitialiseBlocks\","
            "\"xPortGetFreeHeapSize\",\"xPortStartScheduler\","
            "\"vPortEndScheduler\"]}\n",
            ( unsigned ) ( sizeof( unsigned long ) * 8U ),
            ( unsigned ) ( sizeof( portTickType ) * 8U ),
            ( unsigned ) ( sizeof( unsigned portBASE_TYPE ) * 8U ) );
    fflush( stdout );

    trace_scenario = "meta";
    trace_step = "abi_gate";
    trace_check(
        "abi.tick_is_exactly_32_bit",
        sizeof( portTickType ) == 4U && portMAX_DELAY == UINT32_MAX );
    trace_check(
        "abi.port_base_is_exactly_32_bit",
        sizeof( unsigned portBASE_TYPE ) == 4U );

    scenario_tick_no_wake();
    scenario_tick_wakes_task();
    scenario_tick_wrap();
    scenario_same_priority_fifo();
    scenario_delay_positive_no_wrap();
    scenario_delay_positive_wrap();

    trace_scenario = "summary";
    trace_step = "complete";
    trace_check( "all.required.scenarios.completed", 1 );
    return 0;
}
