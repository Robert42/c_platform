// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

void wayland_connect()
{

  const int fd = socket(AF_UNIX, SOCK_STREAM, 0);
  LINUX_ASSERT_NE(fd, -1);

  {
    Mem_Region _prev_stack = STACK;

    const char* wayland_socket_dir = getenv("XDG_RUNTIME_DIR");
    const char* wayland_socket_name = getenv("WAYLAND_DISPLAY");
    LINUX_ASSERT_NE(wayland_socket_dir, NULL);
    LINUX_ASSERT_NE(wayland_socket_name, NULL);

    const Path path = path_join(path_from_cstr(wayland_socket_dir), path_from_cstr(wayland_socket_name));

    struct sockaddr* addr = MEM_REGION_ALLOC(&STACK, struct sockaddr);
    MEM_REGION_ALLOC(&STACK, Path); // allcoate enough bytes to store the path

    addr->sa_family = AF_UNIX;
    strcpy(addr->sa_data, path.cstr);

#if 0
    printf("addr->sa_data: `%s`\n", addr->sa_data);
#endif

    int result = connect(fd, addr, sizeof(*addr) + path.len);
    LINUX_ASSERT_NE(result, -1);
    
    STACK = _prev_stack;
  }

  // ==== close again ====
  LINUX_ASSERT_NE(close(fd), -1);
}

