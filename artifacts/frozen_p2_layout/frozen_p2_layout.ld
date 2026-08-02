/* Deterministic, fixed-address ELF32/i386 layout for certificate extraction. */
OUTPUT_FORMAT("elf32-i386")
OUTPUT_ARCH(i386)
ENTRY(eal6_frozen_entry)

PHDRS
{
  text PT_LOAD FLAGS(5); /* read + execute */
  data PT_LOAD FLAGS(6); /* read + write */
}

SECTIONS
{
  . = 0x00100000;

  .text : ALIGN(16)
  {
    *(.text)
    *(SORT_BY_NAME(.text.*))
  } :text

  .rodata : ALIGN(16)
  {
    *(.rodata)
    *(SORT_BY_NAME(.rodata.*))
  } :text

  .note.gnu.build-id : ALIGN(4)
  {
    *(.note.gnu.build-id)
  } :text

  . = ALIGN(0x1000);

  .data : ALIGN(16)
  {
    *(.data)
    *(SORT_BY_NAME(.data.*))
  } :data

  .bss (NOLOAD) : ALIGN(16)
  {
    __eal6_bss_start = .;
    *(.bss)
    *(SORT_BY_NAME(.bss.*))
    *(COMMON)
    __eal6_bss_end = .;
  } :data

  /* Non-allocated evidence sections are retained for independent checking. */
  .debug_aranges 0 : { *(.debug_aranges .debug_aranges.*) }
  .debug_info    0 : { *(.debug_info .debug_info.*) }
  .debug_abbrev  0 : { *(.debug_abbrev .debug_abbrev.*) }
  .debug_line    0 : { *(.debug_line .debug_line.*) }
  .debug_str     0 : { *(.debug_str .debug_str.*) }
  .debug_loc     0 : { *(.debug_loc .debug_loc.*) }
  .debug_ranges  0 : { *(.debug_ranges .debug_ranges.*) }
  .debug_macro   0 : { *(.debug_macro .debug_macro.*) }
  .comment       0 : { *(.comment) }

  /DISCARD/ :
  {
    *(.note.GNU-stack)
    *(.eh_frame)
    *(.eh_frame.*)
  }
}

ASSERT((ADDR(.text) & 15) == 0, "text must be 16-byte aligned")
ASSERT((ADDR(.data) & 15) == 0, "data must be 16-byte aligned")
ASSERT((ADDR(.bss) & 15) == 0, "bss must be 16-byte aligned")
