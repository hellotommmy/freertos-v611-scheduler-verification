#ifndef EAL6_FREERTOS_V611_SCHEDULER_STRING_H
#define EAL6_FREERTOS_V611_SCHEDULER_STRING_H

#include <stddef.h>

/* Parsed by an unscoped task-construction helper; unreachable from all roots. */
char *strncpy( char *pxDestination, const char *pxSource, size_t xCount );
void *memset( void *pxDestination, int iValue, size_t xCount );

#endif /* EAL6_FREERTOS_V611_SCHEDULER_STRING_H */
