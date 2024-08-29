// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#include "file.linux.h"

void* _linux_read_all_bytes_from_fd(int fd, Mem_Region* region)
{
    debug_assert_ptr_ne(region, NULL);
    const usize bytes_available = mem_region_available_bytes(region);
    ssize bytes_read = read(fd, region->begin, bytes_available);
    LINUX_ASSERT_NE(bytes_read, -1);

    void* const data = region->begin;
    region->begin += bytes_read;

    // Add nullterminator
    assert_ptr_lt(region->begin, region->end); // No more space for the nullterminator
    *(u8*)region->begin = 0;
    region->begin++;

    return data;
}

void _create_file_from_bytes(const char* path, const void* bytes, usize num_bytes)
{
  const int fd = open(path, O_WRONLY | O_CREAT | O_TRUNC, 0666);
  LINUX_ASSERT_NE(fd, -1);

  LINUX_ASSERT_NE(write(fd, bytes, num_bytes), -1);
  LINUX_ASSERT_NE(close(fd), -1);
}
