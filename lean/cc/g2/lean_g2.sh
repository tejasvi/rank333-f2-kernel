#!/bin/bash
# the port's build options for the G2 modules (as port tools/build.py: -DElab.async=false); exec keeps the pid for the scheduler's memory sampling
exec "${LEAN:-lean}" -DElab.async=false "$@"
