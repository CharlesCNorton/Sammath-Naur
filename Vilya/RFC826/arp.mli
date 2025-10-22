
type unit0 =
| Tt

val negb : bool -> bool

type nat =
| O
| S of nat

val length : 'a1 list -> nat

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

type sumbool =
| Left
| Right

val add : nat -> nat -> nat

val bool_dec : bool -> bool -> sumbool

val rev : 'a1 list -> 'a1 list

val list_eq_dec : ('a1 -> 'a1 -> sumbool) -> 'a1 list -> 'a1 list -> sumbool

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

module Pos :
 sig
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val pred_N : positive -> n

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : positive -> mask

  val sub_mask : positive -> positive -> mask

  val sub_mask_carry : positive -> positive -> mask

  val mul : positive -> positive -> positive

  val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val eqb : positive -> positive -> bool

  val coq_Nsucc_double : n -> n

  val coq_Ndouble : n -> n

  val coq_lor : positive -> positive -> positive

  val coq_land : positive -> positive -> n

  val shiftl : positive -> n -> positive

  val testbit : positive -> n -> bool

  val eq_dec : positive -> positive -> sumbool
 end

module N :
 sig
  val add : n -> n -> n

  val sub : n -> n -> n

  val mul : n -> n -> n

  val compare : n -> n -> comparison

  val eqb : n -> n -> bool

  val leb : n -> n -> bool

  val ltb : n -> n -> bool

  val div2 : n -> n

  val coq_lor : n -> n -> n

  val coq_land : n -> n -> n

  val shiftl : n -> n -> n

  val shiftr : n -> n -> n

  val testbit : n -> n -> bool

  val eq_dec : n -> n -> sumbool
 end

type byte = n

type word16 = n

val aRP_HRD_ETHERNET : word16

val aRP_PRO_IP : word16

val aRP_OP_REQUEST : word16

val aRP_OP_REPLY : word16

val rARP_OP_REQUEST : word16

val rARP_OP_REPLY : word16

val eTHERNET_ADDR_LEN : byte

val iPV4_ADDR_LEN : byte

val is_valid_opcode : word16 -> bool

val is_valid_arp_opcode : word16 -> bool

type mACAddress =
  byte list
  (* singleton inductive, whose constructor was Build_MACAddress *)

type iPv4Address = { ipv4_a : byte; ipv4_b : byte; ipv4_c : byte;
                     ipv4_d : byte }

val mAC_ZERO : mACAddress

val is_broadcast_mac : mACAddress -> bool

val is_multicast_mac : mACAddress -> bool

val is_zero_ipv4 : iPv4Address -> bool

val mac_eq : mACAddress -> mACAddress -> bool

type aRPPacket = { ar_hrd : word16; ar_pro : word16; ar_hln : byte;
                   ar_pln : byte; ar_op : word16; ar_sha : byte list;
                   ar_spa : byte list; ar_tha : byte list; ar_tpa : byte list }

type aRPEthernetIPv4 = { arp_op : word16; arp_sha : mACAddress;
                         arp_spa : iPv4Address; arp_tha : mACAddress;
                         arp_tpa : iPv4Address }

type aRPCacheEntry = { ace_ip : iPv4Address; ace_mac : mACAddress;
                       ace_ttl : n; ace_static : bool }

type aRPCache = aRPCacheEntry list

val ip_eq : iPv4Address -> iPv4Address -> bool

val lookup_cache : aRPCache -> iPv4Address -> mACAddress option

val update_cache_entry :
  aRPCache -> iPv4Address -> mACAddress -> n -> aRPCache

val add_cache_entry : aRPCache -> iPv4Address -> mACAddress -> n -> aRPCache

val merge_cache_entry : aRPCache -> iPv4Address -> mACAddress -> n -> aRPCache

val rfc826_merge :
  aRPCache -> iPv4Address -> mACAddress -> n -> bool -> aRPCache

val add_static_entry : aRPCache -> iPv4Address -> mACAddress -> aRPCache

val is_static_cache_entry : aRPCache -> iPv4Address -> bool

val list_static_entries : aRPCache -> aRPCacheEntry list

val count_static_entries : aRPCache -> nat

val would_conflict_static_entry :
  aRPCache -> iPv4Address -> mACAddress -> bool

val make_arp_request :
  mACAddress -> iPv4Address -> iPv4Address -> aRPEthernetIPv4

val make_arp_reply :
  mACAddress -> iPv4Address -> mACAddress -> iPv4Address -> aRPEthernetIPv4

val serialize_mac : mACAddress -> byte list

val serialize_ipv4 : iPv4Address -> byte list

val split_word16 : word16 -> byte list

val combine_word16 : byte -> byte -> word16

val serialize_arp_packet : aRPEthernetIPv4 -> byte list

val parse_arp_packet : byte list -> aRPEthernetIPv4 option

val is_supported_hw_proto : word16 -> word16 -> bool

val process_generic_arp : aRPPacket -> aRPEthernetIPv4 option

val convert_to_generic : aRPEthernetIPv4 -> aRPPacket

type aRPError =
| ErrInvalidOpcode of word16
| ErrBroadcastSender
| ErrMulticastSender
| ErrZeroSPANonRequest
| ErrReplyWrongTHA of mACAddress * mACAddress
| ErrCacheFull of nat
| ErrFloodLimitExceeded of iPv4Address * n
| ErrStaticEntryConflict of iPv4Address
| ErrDuplicateIP of iPv4Address * mACAddress
| ErrInvalidPacketLength of nat
| ErrUnsupportedHardware of word16
| ErrUnsupportedProtocol of word16

type 'a aRPResult =
| ARPSuccess of 'a
| ARPFailure of aRPError

val validate_arp_packet : aRPEthernetIPv4 -> mACAddress -> bool

val validate_arp_packet_detailed :
  aRPEthernetIPv4 -> mACAddress -> unit0 aRPResult

type validatedARPPacket =
  aRPEthernetIPv4
  (* singleton inductive, whose constructor was Build_ValidatedARPPacket *)

val mk_validated_arp :
  mACAddress -> aRPEthernetIPv4 -> validatedARPPacket option

val dEFAULT_ARP_TTL : n

type aRPContext = { arp_my_mac : mACAddress; arp_my_ip : iPv4Address;
                    arp_cache : aRPCache; arp_cache_ttl : n }

type gratuitousARPType =
| NotGratuitous
| GratuitousRequest
| GratuitousReply

val is_gratuitous_arp : aRPEthernetIPv4 -> bool

val classify_gratuitous_arp : aRPEthernetIPv4 -> gratuitousARPType

val is_gratuitous_request : aRPEthernetIPv4 -> bool

val is_gratuitous_reply : aRPEthernetIPv4 -> bool

val flush_cache : aRPCache

val flush_dynamic_entries : aRPCache -> aRPCache

val update_cache_ttl : aRPCache -> n -> aRPCache

val set_context_ttl : aRPContext -> n -> aRPContext

val flush_context_cache : aRPContext -> aRPContext

val flush_context_dynamic : aRPContext -> aRPContext

val get_cache_size : aRPCache -> nat

val get_static_count : aRPCache -> nat

val get_dynamic_count : aRPCache -> nat

val process_arp_packet :
  aRPContext -> aRPEthernetIPv4 -> aRPContext*aRPEthernetIPv4 option

val process_validated_arp_packet :
  aRPContext -> validatedARPPacket -> aRPContext*aRPEthernetIPv4 option

val parse_validated_arp_packet :
  mACAddress -> byte list -> validatedARPPacket option

type rARPMapping = { rarp_mac : mACAddress; rarp_ip : iPv4Address }

type rARPTable = rARPMapping list

val lookup_rarp_table : rARPTable -> mACAddress -> iPv4Address option

val validate_rarp_client : aRPEthernetIPv4 -> mACAddress -> bool

val validate_rarp_server : aRPEthernetIPv4 -> bool

val validate_rarp_packet : aRPEthernetIPv4 -> mACAddress -> bool

val process_rarp_client :
  aRPContext -> aRPEthernetIPv4 -> aRPContext*iPv4Address option

val process_rarp_server :
  aRPContext -> rARPTable -> aRPEthernetIPv4 -> aRPContext*aRPEthernetIPv4
  option

val process_rarp_packet :
  aRPContext -> aRPEthernetIPv4 -> aRPContext*iPv4Address option

type validatedRARPClient =
  aRPEthernetIPv4
  (* singleton inductive, whose constructor was Build_ValidatedRARPClient *)

type validatedRARPServer =
  aRPEthernetIPv4
  (* singleton inductive, whose constructor was Build_ValidatedRARPServer *)

val mk_validated_rarp_client :
  mACAddress -> aRPEthernetIPv4 -> validatedRARPClient option

val mk_validated_rarp_server : aRPEthernetIPv4 -> validatedRARPServer option

val make_gratuitous_arp : mACAddress -> iPv4Address -> aRPEthernetIPv4

val is_suspicious_arp : aRPCache -> aRPEthernetIPv4 -> bool

val aRP_REQUEST_TIMEOUT : n

val aRP_MAX_RETRIES : n

val aRP_PROBE_WAIT : n

val aRP_PROBE_NUM : n

val aRP_PROBE_MIN : n

val aRP_ANNOUNCE_WAIT : n

val aRP_ANNOUNCE_NUM : n

val aRP_ANNOUNCE_INTERVAL : n

val aRP_DEFEND_INTERVAL : n

val aRP_CONFLICT_RECOVERY_WAIT : n

type aRPTimer = { timer_start : n; timer_duration : n; timer_active : bool }

val timer_expired : aRPTimer -> n -> bool

val start_timer : n -> n -> aRPTimer

val stop_timer : aRPTimer -> aRPTimer

type pendingRequest = { preq_target_ip : iPv4Address; preq_retries : 
                        n; preq_timer : aRPTimer }

type probeState = { probe_ip : iPv4Address; probe_count : n;
                    probe_timer : aRPTimer }

type announceState = { announce_count : n; announce_timer : aRPTimer }

type defendState =
  n
  (* singleton inductive, whose constructor was Build_DefendState *)

type aRPStateData =
| StateIdle
| StatePending of pendingRequest list
| StateProbe of probeState
| StateAnnounce of announceState
| StateDefend of defendState
| StateConflict of iPv4Address * aRPTimer

type networkInterface = { if_mac : mACAddress; if_ip : iPv4Address;
                          if_mtu : n; if_up : bool }

type interfaceID = n

type networkInterfaceEx = { ifex_id : interfaceID; ifex_mac : mACAddress;
                            ifex_ip : iPv4Address; ifex_mtu : n;
                            ifex_up : bool; ifex_cache : aRPCache;
                            ifex_cache_ttl : n; ifex_state_data : aRPStateData }

type interfaceTable = networkInterfaceEx list

type floodEntry = { fe_ip : iPv4Address; fe_last_request : n;
                    fe_request_count : n }

type floodTable = floodEntry list

type multiInterfaceARPContext = { mi_interfaces : interfaceTable;
                                  mi_global_flood_table : floodTable;
                                  mi_last_cleanup : n }

val lookup_interface :
  interfaceTable -> interfaceID -> networkInterfaceEx option

val lookup_interface_by_mac :
  interfaceTable -> mACAddress -> networkInterfaceEx option

val lookup_interface_by_ip :
  interfaceTable -> iPv4Address -> networkInterfaceEx option

val is_local_ip : interfaceTable -> iPv4Address -> bool

val select_interface_for_target :
  interfaceTable -> iPv4Address -> networkInterfaceEx option

val get_up_interfaces : interfaceTable -> interfaceTable

val count_interfaces : interfaceTable -> nat

val count_up_interfaces : interfaceTable -> nat

val update_interface : interfaceTable -> networkInterfaceEx -> interfaceTable

val update_interface_cache :
  networkInterfaceEx -> aRPCache -> networkInterfaceEx

val update_interface_state :
  networkInterfaceEx -> aRPStateData -> networkInterfaceEx

val set_interface_up : networkInterfaceEx -> bool -> networkInterfaceEx

val remove_interface : interfaceTable -> interfaceID -> interfaceTable

val add_interface : interfaceTable -> networkInterfaceEx -> interfaceTable

val process_arp_packet_on_interface :
  networkInterfaceEx -> aRPEthernetIPv4 -> networkInterfaceEx*aRPEthernetIPv4
  option

val process_arp_packet_multi :
  multiInterfaceARPContext -> aRPEthernetIPv4 ->
  multiInterfaceARPContext*(interfaceID*aRPEthernetIPv4) option

val send_arp_request_from_interface :
  networkInterfaceEx -> iPv4Address -> aRPEthernetIPv4

val check_interface_caches :
  interfaceTable -> iPv4Address -> (interfaceID*mACAddress) option

val resolve_address_multi :
  multiInterfaceARPContext -> iPv4Address -> (interfaceID*mACAddress)
  option*(interfaceID*aRPEthernetIPv4) option

val create_interface :
  interfaceID -> mACAddress -> iPv4Address -> n -> networkInterfaceEx

val bring_interface_up :
  multiInterfaceARPContext -> interfaceID -> multiInterfaceARPContext

val bring_interface_down :
  multiInterfaceARPContext -> interfaceID -> multiInterfaceARPContext

val flush_interface_cache :
  multiInterfaceARPContext -> interfaceID -> multiInterfaceARPContext

val flush_all_interface_caches :
  multiInterfaceARPContext -> multiInterfaceARPContext

val add_interface_to_context :
  multiInterfaceARPContext -> networkInterfaceEx -> multiInterfaceARPContext

val remove_interface_from_context :
  multiInterfaceARPContext -> interfaceID -> multiInterfaceARPContext

val total_cache_entries : multiInterfaceARPContext -> nat

type enhancedARPContext = { earp_my_mac : mACAddress;
                            earp_my_ip : iPv4Address; earp_cache : aRPCache;
                            earp_cache_ttl : n;
                            earp_state_data : aRPStateData;
                            earp_iface : networkInterface;
                            earp_flood_table : floodTable;
                            earp_last_cache_cleanup : n }

val set_enhanced_context_ttl : enhancedARPContext -> n -> enhancedARPContext

val flush_enhanced_cache : enhancedARPContext -> enhancedARPContext

val flush_enhanced_dynamic : enhancedARPContext -> enhancedARPContext

val disable_dad : enhancedARPContext -> enhancedARPContext

val reset_flood_table : enhancedARPContext -> enhancedARPContext

val single_to_multi : aRPContext -> interfaceID -> multiInterfaceARPContext

val enhanced_to_multi :
  enhancedARPContext -> interfaceID -> multiInterfaceARPContext

val aRP_FLOOD_WINDOW : n

val aRP_FLOOD_THRESHOLD : n

val flood_eq : iPv4Address -> iPv4Address -> bool

val lookup_flood_entry : floodTable -> iPv4Address -> floodEntry option

val update_flood_table : floodTable -> iPv4Address -> n -> floodTable*bool

val clean_flood_table : floodTable -> n -> floodTable

val add_pending_request :
  enhancedARPContext -> iPv4Address -> n -> enhancedARPContext

val remove_pending_request :
  pendingRequest list -> iPv4Address -> pendingRequest list

val retry_pending_request : pendingRequest -> n -> pendingRequest

val process_timeouts :
  enhancedARPContext -> n -> enhancedARPContext*aRPEthernetIPv4 list

val resolve_address :
  enhancedARPContext -> iPv4Address -> n -> (mACAddress
  option*enhancedARPContext)*aRPEthernetIPv4 option

val start_dad_probe :
  enhancedARPContext -> iPv4Address -> n -> enhancedARPContext

val make_arp_probe : mACAddress -> iPv4Address -> aRPEthernetIPv4

val process_probe_timeout :
  enhancedARPContext -> probeState -> n -> enhancedARPContext*aRPEthernetIPv4
  option

val detect_probe_conflict :
  enhancedARPContext -> probeState -> aRPEthernetIPv4 -> bool

val process_announce_timeout :
  enhancedARPContext -> announceState -> n ->
  enhancedARPContext*aRPEthernetIPv4 option

val detect_address_conflict : enhancedARPContext -> aRPEthernetIPv4 -> bool

val can_defend : defendState -> n -> bool

val make_defend_packet : enhancedARPContext -> aRPEthernetIPv4

val process_conflict :
  enhancedARPContext -> n -> enhancedARPContext*aRPEthernetIPv4 option

val send_arp_request_with_flood_check :
  enhancedARPContext -> iPv4Address -> n ->
  enhancedARPContext*aRPEthernetIPv4 option

val age_cache : aRPCache -> n -> aRPCache

val age_all_interface_caches :
  multiInterfaceARPContext -> n -> multiInterfaceARPContext

val process_arp_packet_enhanced :
  enhancedARPContext -> aRPEthernetIPv4 -> n -> n ->
  enhancedARPContext*aRPEthernetIPv4 option

val send_arp_on_interface : networkInterface -> aRPEthernetIPv4 -> bool

type networkEvent =
| SendPacket of aRPPacket
| ReceivePacket of aRPPacket
| Timeout of n

type networkNode = { node_ctx : aRPContext; node_time : n }

val process_event : networkNode -> networkEvent -> networkNode

type enhancedEvent =
| EPacketIn of aRPEthernetIPv4
| ETimerTick of n
| EProbeTimeout
| EAnnounceTimeout
| ERequestTimeout

type enhancedNode = { enode_ctx : enhancedARPContext; enode_time : n }

val enhanced_process_event :
  enhancedNode -> enhancedEvent -> enhancedNode*aRPEthernetIPv4 list
