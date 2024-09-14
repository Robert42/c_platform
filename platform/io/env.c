// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

const char* getenv_or_panic(const char* name)
{
  const char* value = secure_getenv(name);
  if(UNLIKELY(value == NULL))
    PANIC("Environment variable `%s` not set.", name);
  return value;
}

const char* getenv_or_default(const char* name, const char* default_value)
{
  const char* value = secure_getenv(name);
  return value!=NULL ? value : default_value;
}

