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
}
