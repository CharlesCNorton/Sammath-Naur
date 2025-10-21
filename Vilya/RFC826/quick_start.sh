#!/bin/bash
################################################################################
# Quick Start Script for Formally Verified ARP Daemon
################################################################################

set -e

echo "════════════════════════════════════════════════════════════"
echo "  Formally Verified ARP Daemon - Quick Start"
echo "════════════════════════════════════════════════════════════"
echo ""

# Check if running as administrator/root
if [ "$EUID" -ne 0 ] && [ "$(uname)" != "CYGWIN"* ]; then
  echo "⚠ This script requires administrator/root privileges"
  echo "  Please run with sudo or as Administrator"
  exit 1
fi

# Build if needed
if [ ! -f "arp_daemon.exe" ]; then
  echo "📦 Building ARP daemon..."
  make dev
  echo ""
fi

# List devices
echo "📡 Detecting network interfaces..."
./list_devices.exe

echo ""
echo "════════════════════════════════════════════════════════════"
echo "  Select Network Interface"
echo "════════════════════════════════════════════════════════════"
echo ""
read -p "Enter interface number: " IFACE_NUM

# This would require parsing list_devices output
# For now, prompt for manual entry
echo ""
echo "════════════════════════════════════════════════════════════"
echo "  Configuration"
echo "════════════════════════════════════════════════════════════"
echo ""
read -p "Enter interface device name: " DEVICE
read -p "Enter MAC address (AA:BB:CC:DD:EE:FF): " MAC
read -p "Enter IP address (192.168.1.100): " IP

echo ""
echo "════════════════════════════════════════════════════════════"
echo "  Starting ARP Daemon"
echo "════════════════════════════════════════════════════════════"
echo "  Interface: $DEVICE"
echo "  MAC: $MAC"
echo "  IP: $IP"
echo "════════════════════════════════════════════════════════════"
echo ""
echo "Press Ctrl+C to stop"
echo ""

./arp_daemon.exe "$DEVICE" "$MAC" "$IP"
