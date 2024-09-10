// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

void fmt_test()
{
  {
    char BUFFER[1024] = {42};

    Fmt f = fmt_new(BUFFER, sizeof(BUFFER));

    assert_cstr_eq(f.begin, "");

    fmt_write(&f, "player");
    fmt_write(&f, ".pos");
    assert_cstr_eq(f.begin, "player.pos");

    // clean
    fmt_clear(&f);
    assert_ptr_eq(f.end, f.begin);
    assert_cstr_eq(f.begin, "");
    fmt_write(&f, "npc");
    fmt_write(&f, ".pos");
    assert_cstr_eq(f.begin, "npc.pos");
  }

  {
    u8 BUFFER[42] = {37};
    Mem_Region region = MEM_REGION_FROM_ARRAY(BUFFER);

    Fmt f = fmt_new_from_region(&region, 32);
    assert_usize_eq(mem_region_available_bytes(region), 10);

    assert_cstr_eq(f.begin, "");

    fmt_write(&f, "player");
    fmt_write(&f, ".pos");
    assert_cstr_eq(f.begin, "player.pos");
  }

  // indent
  {
    char BUFFER[1024] = {42};

    Fmt f = fmt_new(BUFFER, sizeof(BUFFER));

    fmt_write(&f, "void main()\n");
    fmt_write(&f, "{\n");
    f.indent++;
    fmt_write(&f, "puts(msg);\n");
    fmt_write(&f, "\n");
    fmt_write(&f, "return 0;\n");
    f.indent--;
    fmt_write(&f, "}\n");

    assert_cstr_eq(f.begin, "void main()\n{\n  puts(msg);\n\n  return 0;\n}\n");
  }
}
