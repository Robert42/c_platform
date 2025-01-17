// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#include "file.linux.h"

void mkpath(Path p)
{
  int result = mkdir(p.cstr, 0777);
  if(result!=-1 || errno == EEXIST)
    return;

  if(strchr(p.cstr, '/') && errno==ENOENT)
  {
    mkpath(path_parent(p));
    LINUX_ASSERT_NE(mkdir(p.cstr, 0777), -1);
  }else
  {
    printf("errno: %i\n", errno);
    __linux_call_failed__("mkdir", __FILE__, __LINE__);
  }
}

Bytes_Mut _linux_read_all_bytes_from_fd(int fd, Mem_Region* region)
{
    debug_assert_ptr_ne(region, NULL);
    const usize bytes_available = mem_region_available_bytes(*region);
    ssize bytes_read = read(fd, region->begin, bytes_available);
    LINUX_ASSERT_NE(bytes_read, -1);

    void* const data = region->begin;
    region->begin += bytes_read;

    // Add nullterminator
    assert_ptr_lt(region->begin, region->end); // No more space for the nullterminator
    *(u8*)region->begin = 0;
    region->begin++;

    return (Bytes_Mut){
      .begin = data,
      .end = (u8*)data + bytes_read,
    };
}

Bytes_Mut _read_all_file_bytes(const char* path, Mem_Region* region)
{
  const int fd = open(path, O_RDONLY);
  LINUX_ASSERT_NE(fd, -1);

  Bytes_Mut data = _linux_read_all_bytes_from_fd(fd, region);
  
  LINUX_ASSERT_NE(close(fd), -1);

  return data;
}

void _create_file_from_bytes(const char* path, const void* bytes, usize num_bytes)
{
  const int fd = open(path, O_WRONLY | O_CREAT | O_TRUNC, 0666);
  LINUX_ASSERT_NE(fd, -1);

  LINUX_ASSERT_NE(write(fd, bytes, num_bytes), -1);
  LINUX_ASSERT_NE(close(fd), -1);
}

ssize _file_size(const char* path)
{
  struct stat s;
  int result = stat(path, &s);
  if(result == -1 && errno==ENOENT)
    return -1; // -1, if the file does not exist
  LINUX_ASSERT_NE(result, -1);

  return s.st_size;
}
