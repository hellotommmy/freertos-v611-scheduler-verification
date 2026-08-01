#include <assert.h>
#include <stdio.h>

#include "FreeRTOS.h"
#include "list.h"

typedef struct NamedItem {
    const char *name;
    xListItem item;
} NamedItem;

static const char *item_name(
    const xList *list,
    const NamedItem *items,
    unsigned count,
    const volatile xListItem *item)
{
    unsigned index;
    if (item == (const volatile xListItem *)&list->xListEnd) {
        return "END";
    }
    for (index = 0; index < count; ++index) {
        if (item == &items[index].item) {
            return items[index].name;
        }
    }
    return "UNKNOWN";
}

static void dump_list(
    const char *step,
    const xList *list,
    const NamedItem *items,
    unsigned item_count)
{
    const volatile xListItem *sentinel =
        (const volatile xListItem *)&list->xListEnd;
    const volatile xListItem *node = list->xListEnd.pxNext;
    unsigned visited = 0;

    printf("{\"step\":\"%s\",\"count\":%lu,\"cursor\":\"%s\",\"ring\":[",
           step,
           (unsigned long)list->uxNumberOfItems,
           item_name(list, items, item_count, list->pxIndex));
    while (node != sentinel) {
        assert(visited < item_count);
        assert(node->pxNext->pxPrevious == node);
        assert(node->pxPrevious->pxNext == node);
        assert(node->pvContainer == (const void *)list);
        if (visited != 0) {
            putchar(',');
        }
        printf("{\"id\":\"%s\",\"key\":%lu}",
               item_name(list, items, item_count, node),
               (unsigned long)node->xItemValue);
        node = node->pxNext;
        ++visited;
    }
    assert(visited == (unsigned)list->uxNumberOfItems);
    assert(list->xListEnd.pxNext->pxPrevious == sentinel);
    assert(list->xListEnd.pxPrevious->pxNext == sentinel);
    printf("]}\n");
}

static void init_named(NamedItem *item, const char *name, portTickType key)
{
    item->name = name;
    vListInitialiseItem(&item->item);
    listSET_LIST_ITEM_OWNER(&item->item, item);
    listSET_LIST_ITEM_VALUE(&item->item, key);
}

int main(void)
{
    xList ordered;
    xList fifo;
    NamedItem ordered_items[3];
    NamedItem fifo_items[2];
    NamedItem *next_owner = NULL;

    vListInitialise(&ordered);
    init_named(&ordered_items[0], "A", (portTickType)3);
    init_named(&ordered_items[1], "B", (portTickType)3);
    init_named(&ordered_items[2], "MAX", portMAX_DELAY);
    dump_list("ordered.empty", &ordered, ordered_items, 3);

    vListInsert(&ordered, &ordered_items[0].item);
    dump_list("ordered.insert.A3", &ordered, ordered_items, 3);
    vListInsert(&ordered, &ordered_items[1].item);
    dump_list("ordered.insert.B3.stable", &ordered, ordered_items, 3);
    vListInsert(&ordered, &ordered_items[2].item);
    dump_list("ordered.insert.MAX.boundary", &ordered, ordered_items, 3);
    vListRemove(&ordered_items[1].item);
    assert(ordered_items[1].item.pvContainer == NULL);
    dump_list("ordered.remove.B", &ordered, ordered_items, 3);

    vListInitialise(&fifo);
    /* Deliberately descending keys: insert-end is FIFO, not an ordered-list op. */
    init_named(&fifo_items[0], "F1", (portTickType)9);
    init_named(&fifo_items[1], "F2", (portTickType)1);
    vListInsertEnd(&fifo, &fifo_items[0].item);
    vListInsertEnd(&fifo, &fifo_items[1].item);
    dump_list("fifo.insert_end.F1.F2", &fifo, fifo_items, 2);

    listGET_OWNER_OF_NEXT_ENTRY(next_owner, &fifo);
    assert(next_owner == &fifo_items[0]);
    dump_list("fifo.next.F1", &fifo, fifo_items, 2);
    listGET_OWNER_OF_NEXT_ENTRY(next_owner, &fifo);
    assert(next_owner == &fifo_items[1]);
    dump_list("fifo.next.F2", &fifo, fifo_items, 2);

    vListRemove(&fifo_items[1].item);
    assert(fifo.pxIndex == &fifo_items[0].item);
    dump_list("fifo.remove.cursor.F2", &fifo, fifo_items, 2);
    return 0;
}
