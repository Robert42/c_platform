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
}
